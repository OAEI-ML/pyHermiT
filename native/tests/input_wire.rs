// Compile the isolated production decoder before `lib.rs` integration lands.
// SPDX-License-Identifier: LGPL-3.0-or-later

#[allow(dead_code)]
#[path = "../src/input_wire.rs"]
mod input_wire;

use input_wire::{decode_config, decode_delta, decode_ontology, decode_query, DecodeLimits};
use sha2::{Digest, Sha256};

fn config_document(payload: &[u8]) -> Vec<u8> {
    let offset = 72 + 32;
    let mut bytes = vec![0_u8; offset];
    bytes.extend_from_slice(payload);
    let document_length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    bytes[..8].copy_from_slice(b"PYHMINP\0");
    bytes[8..10].copy_from_slice(&1_u16.to_le_bytes());
    bytes[10..12].copy_from_slice(&2_u16.to_le_bytes());
    bytes[16..24].copy_from_slice(&document_length.to_le_bytes());
    bytes[24..32].copy_from_slice(&72_u64.to_le_bytes());
    bytes[32..36].copy_from_slice(&1_u32.to_le_bytes());
    bytes[72..74].copy_from_slice(&32_u16.to_le_bytes());
    bytes[80..88].copy_from_slice(&u64::try_from(offset).unwrap_or(u64::MAX).to_le_bytes());
    bytes[88..96].copy_from_slice(
        &u64::try_from(payload.len())
            .unwrap_or(u64::MAX)
            .to_le_bytes(),
    );
    bytes[96..100].copy_from_slice(&1_u32.to_le_bytes());
    bytes[100..104].copy_from_slice(&8_u32.to_le_bytes());
    let digest = Sha256::digest(&bytes[72..]);
    bytes[40..72].copy_from_slice(&digest);
    bytes
}

fn config_with_unknown_optional(payload: &[u8]) -> Vec<u8> {
    let mut document = config_document(payload);
    document.splice(104..104, [0_u8; 32]);
    let document_length = u64::try_from(document.len()).unwrap_or(u64::MAX);
    document[16..24].copy_from_slice(&document_length.to_le_bytes());
    document[32..36].copy_from_slice(&2_u32.to_le_bytes());
    document[80..88].copy_from_slice(&136_u64.to_le_bytes());
    document[104..106].copy_from_slice(&65_000_u16.to_le_bytes());
    document[106..108].copy_from_slice(&1_u16.to_le_bytes());
    document[112..120].copy_from_slice(&200_u64.to_le_bytes());
    document[120..128].copy_from_slice(&0_u64.to_le_bytes());
    document[128..132].copy_from_slice(&0_u32.to_le_bytes());
    document[132..136].copy_from_slice(&8_u32.to_le_bytes());
    rehash(&mut document);
    document
}

#[test]
fn config_decoder_owns_and_validates_every_field() {
    let mut payload = vec![0_u8; 64];
    payload[32..40].copy_from_slice(&2.5_f64.to_le_bytes());
    payload[40..48].copy_from_slice(&4096_u64.to_le_bytes());
    payload[48..52].copy_from_slice(&3_u32.to_le_bytes());
    payload[52..54].copy_from_slice(&0b11_1111_u16.to_le_bytes());
    payload[54..60].copy_from_slice(&[2, 1, 0, 1, 2, 2]);
    let decoded = decode_config(config_document(&payload), &DecodeLimits::default());
    assert!(decoded.is_ok(), "valid config failed: {decoded:?}");
    let Some(decoded) = decoded.ok() else {
        return;
    };
    assert_eq!(decoded.timeout_seconds, Some(2.5));
    assert_eq!(decoded.max_memory_bytes, Some(4096));
    assert_eq!(decoded.workers, 3);
    assert!(decoded.buffer_changes);
    assert!(decoded.disjunction_learning);
    assert!(decoded.force_quasi_order_classification);
    assert!(decoded.deterministic);
}

#[test]
fn hostile_counts_lengths_hashes_and_enums_are_rejected() {
    let valid = config_document(&[0_u8; 64]);
    for offset in [0_usize, 8, 10, 16, 24, 32, 40, 72, 80, 88, 96, 100] {
        let mut corrupt = valid.clone();
        corrupt[offset] ^= 0xff;
        assert!(decode_config(corrupt, &DecodeLimits::default()).is_err());
    }
    let mut hostile_count = valid;
    hostile_count[96..100].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(decode_config(hostile_count, &DecodeLimits::default()).is_err());

    let mut invalid_enum = [0_u8; 64];
    invalid_enum[54] = u8::MAX;
    assert!(decode_config(config_document(&invalid_enum), &DecodeLimits::default()).is_err());
}

#[test]
fn unknown_optional_diagnostics_are_skipped_but_unknown_required_sections_fail() {
    let optional = config_with_unknown_optional(&[0_u8; 64]);
    assert!(decode_config(optional.clone(), &DecodeLimits::default()).is_ok());
    let mut required = optional;
    required[106..108].copy_from_slice(&0_u16.to_le_bytes());
    rehash(&mut required);
    assert!(decode_config(required, &DecodeLimits::default()).is_err());
}

fn decode_hex(value: &str) -> Vec<u8> {
    value
        .as_bytes()
        .chunks_exact(2)
        .filter_map(|pair| {
            let text = std::str::from_utf8(pair).ok()?;
            u8::from_str_radix(text, 16).ok()
        })
        .collect()
}

fn golden_document(name: &str) -> Vec<u8> {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("../../tests/data/native-input-v1.json"))
            .unwrap_or(serde_json::Value::Null);
    let encoded = fixture
        .get("documents")
        .and_then(|documents| documents.get(name))
        .and_then(|document| document.get("hex"))
        .and_then(serde_json::Value::as_str)
        .unwrap_or("");
    decode_hex(encoded)
}

fn section_offset(document: &[u8], wanted: u16) -> Option<usize> {
    let count = u32::from_le_bytes(document.get(32..36)?.try_into().ok()?);
    for index in 0..count {
        let start = 72 + usize::try_from(index).ok()?.checked_mul(32)?;
        let kind = u16::from_le_bytes(document.get(start..start + 2)?.try_into().ok()?);
        if kind == wanted {
            let raw = u64::from_le_bytes(document.get(start + 8..start + 16)?.try_into().ok()?);
            return usize::try_from(raw).ok();
        }
    }
    None
}

fn rehash(document: &mut [u8]) {
    let digest = Sha256::digest(&document[72..]);
    document[40..72].copy_from_slice(&digest);
}

fn enlarge_string_pool(mut document: Vec<u8>, additional: usize) -> Option<Vec<u8>> {
    let count = u32::from_le_bytes(document.get(32..36)?.try_into().ok()?);
    let mut string_entry = None;
    let mut original_offsets = Vec::new();
    for index in 0..count {
        let start = 72 + usize::try_from(index).ok()?.checked_mul(32)?;
        let kind = u16::from_le_bytes(document.get(start..start + 2)?.try_into().ok()?);
        let offset = u64::from_le_bytes(document.get(start + 8..start + 16)?.try_into().ok()?);
        original_offsets.push((start, offset));
        if kind == 2 {
            string_entry = Some(start);
        }
    }
    let entry = string_entry?;
    let offset = usize::try_from(u64::from_le_bytes(
        document.get(entry + 8..entry + 16)?.try_into().ok()?,
    ))
    .ok()?;
    let length = usize::try_from(u64::from_le_bytes(
        document.get(entry + 16..entry + 24)?.try_into().ok()?,
    ))
    .ok()?;
    let insert_at = offset.checked_add(length)?;
    document.splice(insert_at..insert_at, std::iter::repeat_n(b'x', additional));
    let additional_u64 = u64::try_from(additional).ok()?;
    let new_length = u64::try_from(length).ok()?.checked_add(additional_u64)?;
    let new_count = u32::try_from(new_length).ok()?;
    document[entry + 16..entry + 24].copy_from_slice(&new_length.to_le_bytes());
    document[entry + 24..entry + 28].copy_from_slice(&new_count.to_le_bytes());
    for (start, original) in original_offsets {
        if usize::try_from(original).ok()? > offset {
            let shifted = original.checked_add(additional_u64)?;
            document[start + 8..start + 16].copy_from_slice(&shifted.to_le_bytes());
        }
    }
    let total = u64::try_from(document.len()).ok()?;
    document[16..24].copy_from_slice(&total.to_le_bytes());
    rehash(&mut document);
    Some(document)
}

#[test]
fn python_golden_decodes_to_complete_owned_semantic_records() {
    let decoded = decode_ontology(golden_document("ontology"), &DecodeLimits::default());
    assert!(decoded.is_ok(), "golden decode failed: {decoded:?}");
    let Some(ontology) = decoded.ok() else {
        return;
    };
    assert_eq!(ontology.program.predicates.len(), 1);
    assert_eq!(ontology.program.positive_facts.len(), 2);
    assert_eq!(ontology.program.ground_disjunctions.len(), 1);
    assert_eq!(ontology.program.role_model.object_role_count, 2);
    assert_eq!(ontology.program.role_model.automata.len(), 1);
    assert_eq!(ontology.program.role_model.automata[0].transitions.len(), 2);
    assert_eq!(ontology.named_individuals, [0, 1]);
    assert!(!ontology
        .program
        .datatype_model
        .semantic_payload_json
        .is_empty());

    let datatype = decode_ontology(
        golden_document("ontology_datatype"),
        &DecodeLimits::default(),
    );
    assert!(datatype.is_ok(), "datatype golden failed: {datatype:?}");
    let Some(datatype) = datatype.ok() else {
        return;
    };
    assert_eq!(datatype.program.datatype_model.literal_identities.len(), 2);
    assert_eq!(
        datatype.program.datatype_model.literal_identities[0].data_identity_id,
        datatype.program.datatype_model.literal_identities[1].data_identity_id
    );
}

#[test]
fn python_config_query_and_delta_goldens_decode_without_callbacks() {
    let ontology = decode_ontology(golden_document("ontology"), &DecodeLimits::default());
    assert!(
        ontology.is_ok(),
        "binding ontology decode failed: {ontology:?}"
    );
    let Some(ontology) = ontology.ok() else {
        return;
    };
    let config = decode_config(golden_document("config"), &DecodeLimits::default());
    assert!(config.is_ok(), "config decode failed: {config:?}");
    let query = decode_query(golden_document("query"), &DecodeLimits::default());
    assert!(query.is_ok(), "query decode failed: {query:?}");
    let Some(query) = query.ok() else {
        return;
    };
    assert_eq!(query.reason.as_deref(), Some("golden overlay"));
    assert_eq!(query.interpretation, ["satisfiable"]);
    assert!(query.program.is_some());
    assert!(query.validate_against(&ontology).is_ok());

    let rebuild = decode_query(golden_document("query_rebuild"), &DecodeLimits::default());
    assert!(rebuild.is_ok(), "rebuild query decode failed: {rebuild:?}");
    let Some(rebuild) = rebuild.ok() else {
        return;
    };
    assert!(rebuild.requires_rebuild);
    assert!(rebuild.program.is_none());
    assert_eq!(rebuild.first_local_predicate_id, 1);
    assert!(rebuild.validate_against(&ontology).is_ok());

    let delta = decode_delta(golden_document("delta"), &DecodeLimits::default());
    assert!(delta.is_ok(), "delta decode failed: {delta:?}");
    let Some(delta) = delta.ok() else {
        return;
    };
    assert_eq!(delta.fact_additions.len(), 1);
    assert_eq!(delta.reasons, ["assertion-only"]);
    assert!(delta.validate_revision(&ontology).is_ok());
}

#[test]
fn semantic_enum_sort_string_and_reference_corruption_is_rejected_after_rehash() {
    let valid = golden_document("ontology");
    let corruptions: &[(u16, usize)] = &[
        (8, 4),   // predicate kind
        (9, 1),   // term sort
        (11, 0),  // ground-atom predicate ID
        (7, 16),  // symbol display offset
        (16, 12), // inverse-role count
    ];
    for (kind, relative) in corruptions {
        let mut corrupt = valid.clone();
        let offset = section_offset(&corrupt, *kind);
        assert!(offset.is_some(), "golden lacks section {kind}");
        let Some(offset) = offset else {
            continue;
        };
        corrupt[offset + relative] = u8::MAX;
        rehash(&mut corrupt);
        assert!(
            decode_ontology(corrupt, &DecodeLimits::default()).is_err(),
            "semantic corruption in section {kind} was accepted"
        );
    }
}

#[test]
fn configured_record_limit_rejects_before_decoded_record_allocation() {
    let limits = DecodeLimits {
        max_records_per_section: 1,
        ..DecodeLimits::default()
    };
    let error = decode_ontology(golden_document("ontology"), &limits);
    assert!(error.is_err());
    assert_eq!(
        error.err().map(|value| value.code),
        Some("NATIVE_INPUT_RESOURCE_LIMIT")
    );
}

#[test]
fn multi_megabyte_bulk_document_decodes_under_explicit_limits() {
    let large = enlarge_string_pool(golden_document("ontology"), 8 * 1024 * 1024);
    assert!(large.is_some());
    let Some(large) = large else {
        return;
    };
    assert!(large.len() > 8 * 1024 * 1024);
    let decoded = decode_ontology(large, &DecodeLimits::default());
    assert!(decoded.is_ok(), "large document failed: {decoded:?}");
}
