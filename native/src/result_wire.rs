//! Versioned compact result buffers returned across the `PyO3` boundary.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeSet;

use sha2::{Digest, Sha256};

use crate::error::{NativeError, NativeResult};
use crate::services::{HierarchyIds, RealizationIds};

pub const RESULT_MAGIC: &[u8; 8] = b"PYHMTRS\0";
pub const RESULT_SCHEMA_VERSION: u16 = 1;
pub const RESULT_HEADER_LEN: usize = 64;
pub const MAX_RESULT_BYTES: usize = 512 * 1024 * 1024;

const CHECK_RECORD_LEN: usize = 64;
const HIERARCHY_PREFIX_LEN: usize = 24;
const REALIZATION_PREFIX_LEN: usize = 40;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum ResultKind {
    Check = 1,
    CheckMany = 2,
    Hierarchy = 3,
    Realization = 4,
    Delta = 5,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckStatistics {
    pub elapsed_nanoseconds: u64,
    pub nodes: u64,
    pub facts: u64,
    pub branches: u64,
    pub backtracks: u64,
    pub merges: u64,
    pub datatype_checks: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckWireResult {
    pub satisfiable: bool,
    pub statistics: CheckStatistics,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RealizationWireResult {
    pub same_as: Vec<Vec<u32>>,
    pub direct_types: Vec<(u32, Vec<u32>)>,
    pub object_targets: Vec<(u32, u32, Vec<u32>)>,
    pub data_targets: Vec<(u32, u32, Vec<u32>)>,
    pub different_from: Vec<(u32, u32)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum DeltaWireOutcome {
    AppliedIncrementally = 1,
    RebuildRequired = 2,
}

pub fn encode_check(result: CheckWireResult) -> NativeResult<Vec<u8>> {
    encode_checks(ResultKind::Check, &[result])
}

pub fn encode_check_many(results: &[CheckWireResult]) -> NativeResult<Vec<u8>> {
    encode_checks(ResultKind::CheckMany, results)
}

fn encode_checks(kind: ResultKind, results: &[CheckWireResult]) -> NativeResult<Vec<u8>> {
    if kind == ResultKind::Check && results.len() != 1 {
        return Err(NativeError::invariant(
            "single-check result requires exactly one record",
        ));
    }
    let payload_length = results
        .len()
        .checked_mul(CHECK_RECORD_LEN)
        .ok_or_else(|| NativeError::invariant("check-result payload length overflow"))?;
    let mut payload = Vec::new();
    payload.try_reserve_exact(payload_length).map_err(|_| {
        NativeError::invariant("check-result payload allocation failed before encoding")
    })?;
    for result in results {
        payload.push(u8::from(result.satisfiable));
        payload.extend_from_slice(&[0; 7]);
        for value in [
            result.statistics.elapsed_nanoseconds,
            result.statistics.nodes,
            result.statistics.facts,
            result.statistics.branches,
            result.statistics.backtracks,
            result.statistics.merges,
            result.statistics.datatype_checks,
        ] {
            payload.extend_from_slice(&value.to_le_bytes());
        }
    }
    finish_document(
        kind,
        usize_to_u32(results.len(), "check result count")?,
        payload,
    )
}

pub fn encode_hierarchy(hierarchy: &HierarchyIds) -> NativeResult<Vec<u8>> {
    hierarchy.validate()?;
    let node_count = usize_to_u32(hierarchy.nodes.len(), "hierarchy node count")?;
    let member_count = hierarchy.nodes.iter().try_fold(0_u32, |total, node| {
        total
            .checked_add(usize_to_u32(node.len(), "hierarchy member count")?)
            .ok_or_else(|| NativeError::invariant("hierarchy member count overflow"))
    })?;
    let edge_count = usize_to_u32(hierarchy.edges.len(), "hierarchy edge count")?;
    let offset_count = hierarchy
        .nodes
        .len()
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant("hierarchy offset count overflow"))?;
    let payload_length = HIERARCHY_PREFIX_LEN
        .checked_add(checked_bytes(offset_count, 4, "hierarchy offsets")?)
        .and_then(|value| {
            value.checked_add(
                usize::try_from(member_count)
                    .unwrap_or(usize::MAX)
                    .saturating_mul(4),
            )
        })
        .and_then(|value| value.checked_add(hierarchy.edges.len().saturating_mul(8)))
        .ok_or_else(|| NativeError::invariant("hierarchy-result payload length overflow"))?;
    let mut payload = Vec::new();
    payload.try_reserve_exact(payload_length).map_err(|_| {
        NativeError::invariant("hierarchy-result payload allocation failed before encoding")
    })?;
    write_u32s(
        &mut payload,
        &[
            node_count,
            member_count,
            edge_count,
            hierarchy.top_node,
            hierarchy.bottom_node,
            0,
        ],
    );
    let mut offset = 0_u32;
    payload.extend_from_slice(&offset.to_le_bytes());
    for node in &hierarchy.nodes {
        offset = offset
            .checked_add(usize_to_u32(node.len(), "hierarchy node size")?)
            .ok_or_else(|| NativeError::invariant("hierarchy member offset overflow"))?;
        payload.extend_from_slice(&offset.to_le_bytes());
    }
    for node in &hierarchy.nodes {
        write_u32s(&mut payload, node);
    }
    for &(child, parent) in &hierarchy.edges {
        let pair: [u32; 2] = (child, parent).into();
        write_u32s(&mut payload, &pair);
    }
    if payload.len() != payload_length {
        return Err(NativeError::invariant(
            "hierarchy-result encoder length accounting diverged",
        ));
    }
    finish_document(ResultKind::Hierarchy, node_count, payload)
}

pub fn encode_realization(result: &RealizationWireResult) -> NativeResult<Vec<u8>> {
    encode_realization_parts(
        &result.same_as,
        &result.direct_types,
        &result.object_targets,
        &result.data_targets,
        &result.different_from,
    )
}

/// Encode an immutable validated realization without cloning its potentially large tables.
pub fn encode_realization_ids(result: &RealizationIds) -> NativeResult<Vec<u8>> {
    encode_realization_parts(
        result.same_as(),
        result.direct_types(),
        result.object_targets(),
        result.data_targets(),
        result.different_from(),
    )
}

fn encode_realization_parts(
    same_as: &[Vec<u32>],
    direct_types: &[(u32, Vec<u32>)],
    object_targets: &[(u32, u32, Vec<u32>)],
    data_targets: &[(u32, u32, Vec<u32>)],
    different_from: &[(u32, u32)],
) -> NativeResult<Vec<u8>> {
    validate_realization_parts(
        same_as,
        direct_types,
        object_targets,
        data_targets,
        different_from,
    )?;
    let group_count = usize_to_u32(same_as.len(), "same-as group count")?;
    let individual_count = count_nested(same_as, "same-as member count")?;
    let direct_value_count = direct_types.iter().try_fold(0_u32, |total, (_, values)| {
        checked_nested_total(total, values.len())
    })?;
    let object_value_count = object_targets
        .iter()
        .try_fold(0_u32, |total, (_, _, values)| {
            checked_nested_total(total, values.len())
        })?;
    let data_value_count = data_targets
        .iter()
        .try_fold(0_u32, |total, (_, _, values)| {
            checked_nested_total(total, values.len())
        })?;
    let direct_count = usize_to_u32(direct_types.len(), "direct-type row count")?;
    let object_count = usize_to_u32(object_targets.len(), "object-target row count")?;
    let data_count = usize_to_u32(data_targets.len(), "data-target row count")?;
    let different_count = usize_to_u32(different_from.len(), "different-from count")?;

    let payload_length = realization_payload_length(RealizationCounts {
        groups: same_as.len(),
        direct_rows: direct_types.len(),
        object_rows: object_targets.len(),
        data_rows: data_targets.len(),
        different_pairs: different_from.len(),
        individual_count,
        direct_value_count,
        object_value_count,
        data_value_count,
    })?;
    let mut payload = Vec::new();
    payload.try_reserve_exact(payload_length).map_err(|_| {
        NativeError::invariant("realization-result payload allocation failed before encoding")
    })?;
    write_u32s(
        &mut payload,
        &[
            group_count,
            individual_count,
            direct_count,
            direct_value_count,
            object_count,
            object_value_count,
            data_count,
            data_value_count,
            different_count,
            0,
        ],
    );
    write_offsets_and_values(&mut payload, same_as.iter().map(Vec::as_slice))?;
    write_rows2(&mut payload, direct_types)?;
    write_rows3(&mut payload, object_targets)?;
    write_rows3(&mut payload, data_targets)?;
    for &(left, right) in different_from {
        let pair: [u32; 2] = (left, right).into();
        write_u32s(&mut payload, &pair);
    }
    if payload.len() != payload_length {
        return Err(NativeError::invariant(
            "realization-result encoder length accounting diverged",
        ));
    }
    finish_document(ResultKind::Realization, group_count, payload)
}

pub fn encode_delta(outcome: DeltaWireOutcome) -> NativeResult<Vec<u8>> {
    let mut payload = vec![outcome as u8];
    payload.extend_from_slice(&[0; 7]);
    finish_document(ResultKind::Delta, 1, payload)
}

fn validate_realization_parts(
    same_as: &[Vec<u32>],
    direct_types: &[(u32, Vec<u32>)],
    object_targets: &[(u32, u32, Vec<u32>)],
    data_targets: &[(u32, u32, Vec<u32>)],
    different_from: &[(u32, u32)],
) -> NativeResult<()> {
    if same_as.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::invariant(
            "same-as groups are not canonically sorted",
        ));
    }
    let mut individuals = BTreeSet::new();
    for group in same_as {
        if group.is_empty() || group.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::invariant(
                "same-as group is empty or noncanonical",
            ));
        }
        if group
            .iter()
            .any(|individual| !individuals.insert(*individual))
        {
            return Err(NativeError::invariant(
                "same-as groups do not partition named individuals",
            ));
        }
    }
    let group_count = usize_to_u32(same_as.len(), "same-as group count")?;
    validate_rows2(direct_types, group_count, "direct-type")?;
    validate_rows3(object_targets, group_count, "object-target")?;
    if object_targets
        .iter()
        .any(|(_, _, targets)| targets.iter().any(|target| *target >= group_count))
    {
        return Err(NativeError::invariant(
            "object-target row references an absent same-as group",
        ));
    }
    validate_rows3(data_targets, group_count, "data-target")?;
    if different_from.windows(2).any(|pair| pair[0] >= pair[1])
        || different_from
            .iter()
            .any(|&(left, right)| left >= right || right >= group_count)
    {
        return Err(NativeError::invariant(
            "different-from group pairs are noncanonical or invalid",
        ));
    }
    Ok(())
}

fn validate_rows2(rows: &[(u32, Vec<u32>)], group_count: u32, label: &str) -> NativeResult<()> {
    if rows.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || rows.iter().any(|(group, values)| {
            *group >= group_count || values.windows(2).any(|pair| pair[0] >= pair[1])
        })
    {
        return Err(NativeError::invariant(format!(
            "{label} rows or values are noncanonical"
        )));
    }
    Ok(())
}

fn validate_rows3(
    rows: &[(u32, u32, Vec<u32>)],
    group_count: u32,
    label: &str,
) -> NativeResult<()> {
    if rows
        .windows(2)
        .any(|pair| (pair[0].0, pair[0].1) >= (pair[1].0, pair[1].1))
        || rows.iter().any(|(group, _, values)| {
            *group >= group_count || values.windows(2).any(|pair| pair[0] >= pair[1])
        })
    {
        return Err(NativeError::invariant(format!(
            "{label} rows or values are noncanonical"
        )));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RealizationCounts {
    groups: usize,
    direct_rows: usize,
    object_rows: usize,
    data_rows: usize,
    different_pairs: usize,
    individual_count: u32,
    direct_value_count: u32,
    object_value_count: u32,
    data_value_count: u32,
}

fn realization_payload_length(counts: RealizationCounts) -> NativeResult<usize> {
    let group_offsets = counts
        .groups
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant("same-as offset count overflow"))?;
    let words = group_offsets
        .checked_add(usize::try_from(counts.individual_count).unwrap_or(usize::MAX))
        .and_then(|value| value.checked_add(counts.direct_rows.saturating_mul(3)))
        .and_then(|value| {
            value.checked_add(usize::try_from(counts.direct_value_count).unwrap_or(usize::MAX))
        })
        .and_then(|value| value.checked_add(counts.object_rows.saturating_mul(4)))
        .and_then(|value| {
            value.checked_add(usize::try_from(counts.object_value_count).unwrap_or(usize::MAX))
        })
        .and_then(|value| value.checked_add(counts.data_rows.saturating_mul(4)))
        .and_then(|value| {
            value.checked_add(usize::try_from(counts.data_value_count).unwrap_or(usize::MAX))
        })
        .and_then(|value| value.checked_add(counts.different_pairs.saturating_mul(2)))
        .ok_or_else(|| NativeError::invariant("realization-result word count overflow"))?;
    REALIZATION_PREFIX_LEN
        .checked_add(checked_bytes(words, 4, "realization payload")?)
        .ok_or_else(|| NativeError::invariant("realization-result payload length overflow"))
}

fn write_rows2(output: &mut Vec<u8>, rows: &[(u32, Vec<u32>)]) -> NativeResult<()> {
    let mut offset = 0_u32;
    for (group, values) in rows {
        let count = usize_to_u32(values.len(), "direct-type value count")?;
        write_u32s(output, &[*group, offset, count]);
        offset = offset
            .checked_add(count)
            .ok_or_else(|| NativeError::invariant("direct-type value offset overflow"))?;
    }
    for (_, values) in rows {
        write_u32s(output, values);
    }
    Ok(())
}

fn write_rows3(output: &mut Vec<u8>, rows: &[(u32, u32, Vec<u32>)]) -> NativeResult<()> {
    let mut offset = 0_u32;
    for (group, property, values) in rows {
        let count = usize_to_u32(values.len(), "property-target value count")?;
        write_u32s(output, &[*group, *property, offset, count]);
        offset = offset
            .checked_add(count)
            .ok_or_else(|| NativeError::invariant("property-target value offset overflow"))?;
    }
    for (_, _, values) in rows {
        write_u32s(output, values);
    }
    Ok(())
}

fn write_offsets_and_values<'a>(
    output: &mut Vec<u8>,
    values: impl Iterator<Item = &'a [u32]> + Clone,
) -> NativeResult<()> {
    let mut offset = 0_u32;
    output.extend_from_slice(&offset.to_le_bytes());
    for row in values.clone() {
        offset = offset
            .checked_add(usize_to_u32(row.len(), "nested row size")?)
            .ok_or_else(|| NativeError::invariant("nested row offset overflow"))?;
        output.extend_from_slice(&offset.to_le_bytes());
    }
    for row in values {
        write_u32s(output, row);
    }
    Ok(())
}

fn finish_document(kind: ResultKind, item_count: u32, payload: Vec<u8>) -> NativeResult<Vec<u8>> {
    let total_length = RESULT_HEADER_LEN
        .checked_add(payload.len())
        .ok_or_else(|| NativeError::invariant("result document length overflow"))?;
    if total_length > MAX_RESULT_BYTES {
        return Err(NativeError::invariant(
            "result document exceeds the native output cap",
        ));
    }
    let mut document = vec![0; RESULT_HEADER_LEN];
    document.extend_from_slice(&payload);
    document[..8].copy_from_slice(RESULT_MAGIC);
    document[8..10].copy_from_slice(&RESULT_SCHEMA_VERSION.to_le_bytes());
    document[10..12].copy_from_slice(&(kind as u16).to_le_bytes());
    document[16..24].copy_from_slice(
        &u64::try_from(total_length)
            .map_err(|_| NativeError::invariant("result length cannot fit u64"))?
            .to_le_bytes(),
    );
    document[24..28].copy_from_slice(&item_count.to_le_bytes());
    let hash = Sha256::digest(&payload);
    document[32..64].copy_from_slice(&hash);
    Ok(document)
}

fn count_nested(values: &[Vec<u32>], label: &str) -> NativeResult<u32> {
    values.iter().try_fold(0_u32, |total, row| {
        total
            .checked_add(usize_to_u32(row.len(), label)?)
            .ok_or_else(|| NativeError::invariant(format!("{label} overflow")))
    })
}

fn checked_nested_total(total: u32, length: usize) -> NativeResult<u32> {
    total
        .checked_add(usize_to_u32(length, "nested result value count")?)
        .ok_or_else(|| NativeError::invariant("nested result value count overflow"))
}

fn checked_bytes(count: usize, width: usize, label: &str) -> NativeResult<usize> {
    count
        .checked_mul(width)
        .ok_or_else(|| NativeError::invariant(format!("{label} byte length overflow")))
}

fn usize_to_u32(value: usize, label: &str) -> NativeResult<u32> {
    u32::try_from(value)
        .map_err(|_| NativeError::invariant(format!("{label} exceeds the u32 wire limit")))
}

fn write_u32s(output: &mut Vec<u8>, values: &[u32]) {
    for value in values {
        output.extend_from_slice(&value.to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_and_batch_records_are_fixed_width_and_hashed() -> NativeResult<()> {
        let first = CheckWireResult {
            satisfiable: true,
            statistics: CheckStatistics {
                elapsed_nanoseconds: 1_500_000_000,
                nodes: 2,
                facts: 3,
                branches: 4,
                backtracks: 5,
                merges: 6,
                datatype_checks: 7,
            },
        };
        let single = encode_check(first)?;
        let batch = encode_check_many(&[
            first,
            CheckWireResult {
                satisfiable: false,
                statistics: CheckStatistics::default(),
            },
        ])?;
        assert_eq!(single.len(), RESULT_HEADER_LEN + CHECK_RECORD_LEN);
        assert_eq!(batch.len(), RESULT_HEADER_LEN + CHECK_RECORD_LEN * 2);
        assert_eq!(&single[..8], RESULT_MAGIC);
        assert_eq!(
            u16::from_le_bytes([single[10], single[11]]),
            ResultKind::Check as u16
        );
        assert_eq!(&single[32..64], Sha256::digest(&single[64..]).as_slice());
        assert_eq!(single[64], 1);
        assert_eq!(batch[64 + CHECK_RECORD_LEN], 0);
        Ok(())
    }

    #[test]
    fn hierarchy_encoding_is_canonical_and_rejects_invalid_dags() -> NativeResult<()> {
        let hierarchy = HierarchyIds {
            nodes: vec![vec![0], vec![1, 2], vec![3]],
            edges: vec![(0, 1), (1, 2)],
            top_node: 2,
            bottom_node: 0,
        };
        let encoded = encode_hierarchy(&hierarchy)?;
        assert_eq!(
            u32::from_le_bytes(
                encoded[64..68]
                    .try_into()
                    .map_err(|_| NativeError::invariant("fixture"))?
            ),
            3
        );
        assert_eq!(encoded.len(), RESULT_HEADER_LEN + 24 + 16 + 16 + 16);
        let invalid = HierarchyIds {
            edges: vec![(0, 2), (0, 1), (1, 2)],
            ..hierarchy
        };
        assert!(encode_hierarchy(&invalid).is_err());
        Ok(())
    }

    #[test]
    fn realization_encodes_every_partition_and_answer_table() -> NativeResult<()> {
        let result = RealizationWireResult {
            same_as: vec![vec![1, 2], vec![7]],
            direct_types: vec![(0, vec![3, 4]), (1, vec![5])],
            object_targets: vec![(0, 9, vec![0, 1])],
            data_targets: vec![(1, 8, vec![11, 12])],
            different_from: vec![(0, 1)],
        };
        let encoded = encode_realization(&result)?;
        assert_eq!(
            u16::from_le_bytes([encoded[10], encoded[11]]),
            ResultKind::Realization as u16
        );
        assert_eq!(
            u32::from_le_bytes(
                encoded[64..68]
                    .try_into()
                    .map_err(|_| NativeError::invariant("fixture"))?
            ),
            2
        );
        let mut invalid = result;
        invalid.same_as = vec![vec![2], vec![1]];
        assert!(encode_realization(&invalid).is_err());
        invalid.same_as = vec![vec![1], vec![2]];
        invalid.object_targets = vec![(0, 9, vec![2])];
        assert!(encode_realization(&invalid).is_err());
        Ok(())
    }

    #[test]
    fn delta_outcomes_have_no_ambiguous_trailing_payload() -> NativeResult<()> {
        for outcome in [
            DeltaWireOutcome::AppliedIncrementally,
            DeltaWireOutcome::RebuildRequired,
        ] {
            let encoded = encode_delta(outcome)?;
            assert_eq!(encoded.len(), RESULT_HEADER_LEN + 8);
            assert_eq!(encoded[64], outcome as u8);
            assert!(encoded[65..].iter().all(|value| *value == 0));
        }
        Ok(())
    }
}
