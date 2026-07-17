//! Bounds-checked, allocation-capped private wire schema.
// SPDX-License-Identifier: LGPL-3.0-or-later
//!
//! The reader owns the exact `Vec<u8>` received from `PyO3`. Section validation uses slices into
//! that one owned buffer and never retains Python memory.  All serialized arithmetic is fixed
//! width and little endian; Rust enum layout and `usize` never cross the boundary.

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use crate::error::{NativeError, NativeResult};
use crate::model::{CoreMetadata, IR_SCHEMA_VERSION};

pub const MAGIC: &[u8; 8] = b"PYHMTIR\0";
pub const HEADER_LEN: usize = 72;
pub const DIRECTORY_ENTRY_LEN: usize = 32;
pub const MAX_WIRE_BYTES: usize = 512 * 1024 * 1024;
pub const MAX_SECTIONS: u32 = 256;
pub const OPTIONAL_SECTION: u16 = 1;

const METADATA_LEN: usize = 144;
const SYMBOL_RECORD_LEN: usize = 16;
const PREDICATE_RECORD_LEN: usize = 16;
const FACT_RECORD_LEN: usize = 16;
const ATOM_RECORD_LEN: usize = 16;
const CLAUSE_RECORD_LEN: usize = 24;
const PROVENANCE_RECORD_LEN: usize = 32;
const U32_NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum DocumentKind {
    Ontology = 1,
    Config = 2,
    Query = 3,
    Delta = 4,
    Result = 5,
}

impl DocumentKind {
    fn parse(value: u16) -> NativeResult<Self> {
        match value {
            1 => Ok(Self::Ontology),
            2 => Ok(Self::Config),
            3 => Ok(Self::Query),
            4 => Ok(Self::Delta),
            5 => Ok(Self::Result),
            _ => Err(NativeError::version(format!(
                "wire document kind {value} is unsupported"
            ))),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u16)]
pub enum SectionKind {
    Metadata = 1,
    Strings = 2,
    Symbols = 3,
    Predicates = 4,
    Facts = 5,
    Atoms = 6,
    Clauses = 7,
    Provenance = 8,
    Config = 32,
    Query = 33,
    Delta = 34,
    Result = 35,
}

impl SectionKind {
    const fn parse(value: u16) -> Option<Self> {
        match value {
            1 => Some(Self::Metadata),
            2 => Some(Self::Strings),
            3 => Some(Self::Symbols),
            4 => Some(Self::Predicates),
            5 => Some(Self::Facts),
            6 => Some(Self::Atoms),
            7 => Some(Self::Clauses),
            8 => Some(Self::Provenance),
            32 => Some(Self::Config),
            33 => Some(Self::Query),
            34 => Some(Self::Delta),
            35 => Some(Self::Result),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Section {
    pub kind: SectionKind,
    pub offset: usize,
    pub length: usize,
    pub count: u32,
    pub alignment: u32,
}

#[derive(Clone, Debug)]
pub struct ValidatedDocument {
    bytes: Vec<u8>,
    pub document_kind: DocumentKind,
    pub sections: BTreeMap<SectionKind, Section>,
    pub metadata: Option<CoreMetadata>,
}

impl ValidatedDocument {
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    #[must_use]
    pub fn section_bytes(&self, kind: SectionKind) -> Option<&[u8]> {
        self.sections.get(&kind).and_then(|section| {
            self.bytes
                .get(section.offset..section.offset + section.length)
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct RawSection {
    raw_kind: u16,
    flags: u16,
    offset: usize,
    length: usize,
    count: u32,
    alignment: u32,
}

pub fn validate_owned(
    bytes: Vec<u8>,
    expected_kind: DocumentKind,
) -> NativeResult<ValidatedDocument> {
    if bytes.len() > MAX_WIRE_BYTES {
        return Err(NativeError::new(
            crate::error::ErrorKind::Resource,
            "NATIVE_WIRE_SIZE_LIMIT",
            "wire document exceeds the native size limit",
        )
        .with_context("observed", bytes.len().to_string())
        .with_context("allowed", MAX_WIRE_BYTES.to_string()));
    }
    let header = bytes
        .get(..HEADER_LEN)
        .ok_or_else(|| NativeError::wire("wire document is shorter than its fixed header"))?;
    if header.get(..8) != Some(MAGIC.as_slice()) {
        return Err(NativeError::wire("wire magic is invalid"));
    }
    let schema = read_u16(header, 8)?;
    if schema != IR_SCHEMA_VERSION {
        return Err(NativeError::version(format!(
            "wire schema {schema} is incompatible with {IR_SCHEMA_VERSION}"
        )));
    }
    let document_kind = DocumentKind::parse(read_u16(header, 10)?)?;
    if document_kind != expected_kind {
        return Err(NativeError::wire(format!(
            "wire document kind {document_kind:?} does not match {expected_kind:?}"
        )));
    }
    if read_u32(header, 12)? != 0 || read_u32(header, 36)? != 0 {
        return Err(NativeError::version(
            "wire header contains unsupported flags or reserved bits",
        ));
    }
    let total_length = u64_to_usize(read_u64(header, 16)?, "total length")?;
    if total_length != bytes.len() {
        return Err(NativeError::wire(
            "wire total length does not match buffer length",
        ));
    }
    let directory_offset = u64_to_usize(read_u64(header, 24)?, "directory offset")?;
    if directory_offset != HEADER_LEN || directory_offset % 8 != 0 {
        return Err(NativeError::wire(
            "wire directory offset is not the canonical aligned header boundary",
        ));
    }
    let section_count = read_u32(header, 32)?;
    if section_count > MAX_SECTIONS {
        return Err(NativeError::wire(
            "wire section count exceeds the validation cap",
        ));
    }
    let directory_length = usize::try_from(section_count)
        .ok()
        .and_then(|count| count.checked_mul(DIRECTORY_ENTRY_LEN))
        .ok_or_else(|| NativeError::wire("wire directory length overflow"))?;
    let directory_end = directory_offset
        .checked_add(directory_length)
        .ok_or_else(|| NativeError::wire("wire directory end overflow"))?;
    if directory_end > bytes.len() {
        return Err(NativeError::wire(
            "wire directory lies outside the document",
        ));
    }
    let expected_hash = header
        .get(40..72)
        .ok_or_else(|| NativeError::wire("wire content hash is truncated"))?;
    let actual_hash = Sha256::digest(
        bytes
            .get(HEADER_LEN..)
            .ok_or_else(|| NativeError::wire("wire payload is unavailable"))?,
    );
    if actual_hash.as_slice() != expected_hash {
        return Err(NativeError::wire(
            "wire content hash does not match payload",
        ));
    }

    let mut raw_sections = Vec::new();
    raw_sections
        .try_reserve_exact(usize::try_from(section_count).unwrap_or(0))
        .map_err(|_| NativeError::wire("wire directory allocation failed"))?;
    for index in 0..section_count {
        let start = directory_offset
            .checked_add(
                usize::try_from(index)
                    .ok()
                    .and_then(|value| value.checked_mul(DIRECTORY_ENTRY_LEN))
                    .ok_or_else(|| NativeError::wire("wire directory index overflow"))?,
            )
            .ok_or_else(|| NativeError::wire("wire directory offset overflow"))?;
        let entry = bytes
            .get(start..start + DIRECTORY_ENTRY_LEN)
            .ok_or_else(|| NativeError::wire("wire directory entry is truncated"))?;
        if read_u32(entry, 4)? != 0 {
            return Err(NativeError::wire("wire section reserved bits are nonzero"));
        }
        let flags = read_u16(entry, 2)?;
        if flags & !OPTIONAL_SECTION != 0 {
            return Err(NativeError::version("wire section has unsupported flags"));
        }
        let alignment = read_u32(entry, 28)?;
        if alignment == 0 || !alignment.is_power_of_two() || alignment > 64 {
            return Err(NativeError::wire("wire section alignment is invalid"));
        }
        let offset = u64_to_usize(read_u64(entry, 8)?, "section offset")?;
        let length = u64_to_usize(read_u64(entry, 16)?, "section length")?;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| NativeError::wire("wire section end overflow"))?;
        if offset < directory_end || end > bytes.len() {
            return Err(NativeError::wire(
                "wire section lies outside its payload area",
            ));
        }
        if offset % usize::try_from(alignment).unwrap_or(usize::MAX) != 0 {
            return Err(NativeError::wire(
                "wire section offset violates its alignment",
            ));
        }
        raw_sections.push(RawSection {
            raw_kind: read_u16(entry, 0)?,
            flags,
            offset,
            length,
            count: read_u32(entry, 24)?,
            alignment,
        });
    }
    validate_non_overlapping(&raw_sections)?;
    validate_zero_padding_and_coverage(&bytes, directory_end, &raw_sections)?;

    let mut sections = BTreeMap::new();
    for raw in raw_sections {
        let Some(kind) = SectionKind::parse(raw.raw_kind) else {
            if raw.flags & OPTIONAL_SECTION != 0 {
                continue;
            }
            return Err(NativeError::version(format!(
                "required wire section kind {} is unknown",
                raw.raw_kind
            )));
        };
        if sections.contains_key(&kind) {
            return Err(NativeError::wire("wire section kind occurs more than once"));
        }
        sections.insert(
            kind,
            Section {
                kind,
                offset: raw.offset,
                length: raw.length,
                count: raw.count,
                alignment: raw.alignment,
            },
        );
    }
    validate_required_sections(document_kind, &sections)?;
    validate_section_records(&bytes, &sections)?;
    validate_cross_references(&bytes, &sections)?;
    let metadata = sections
        .get(&SectionKind::Metadata)
        .map(|section| parse_metadata(&bytes[section.offset..section.offset + section.length]))
        .transpose()?;
    Ok(ValidatedDocument {
        bytes,
        document_kind,
        sections,
        metadata,
    })
}

fn validate_required_sections(
    document_kind: DocumentKind,
    sections: &BTreeMap<SectionKind, Section>,
) -> NativeResult<()> {
    let required: &[SectionKind] = match document_kind {
        DocumentKind::Ontology => &[SectionKind::Metadata],
        DocumentKind::Config => &[SectionKind::Config],
        DocumentKind::Query => &[SectionKind::Query],
        DocumentKind::Delta => &[SectionKind::Delta],
        DocumentKind::Result => &[SectionKind::Result],
    };
    if required.iter().any(|kind| !sections.contains_key(kind)) {
        return Err(NativeError::wire(
            "wire document is missing a required section",
        ));
    }
    Ok(())
}

fn validate_non_overlapping(sections: &[RawSection]) -> NativeResult<()> {
    let mut ranges: Vec<(usize, usize)> = sections
        .iter()
        .map(|section| (section.offset, section.offset + section.length))
        .collect();
    ranges.sort_unstable();
    if ranges.windows(2).any(|pair| pair[0].1 > pair[1].0) {
        return Err(NativeError::wire("wire sections overlap"));
    }
    Ok(())
}

fn validate_zero_padding_and_coverage(
    bytes: &[u8],
    directory_end: usize,
    sections: &[RawSection],
) -> NativeResult<()> {
    let mut ordered: Vec<_> = sections.iter().collect();
    ordered.sort_unstable_by_key(|section| (section.offset, section.length));
    let mut cursor = directory_end;
    for section in ordered {
        let padding = bytes
            .get(cursor..section.offset)
            .ok_or_else(|| NativeError::wire("wire padding range is invalid"))?;
        if padding.iter().any(|byte| *byte != 0) {
            return Err(NativeError::wire("wire alignment padding must be zero"));
        }
        cursor = section
            .offset
            .checked_add(section.length)
            .ok_or_else(|| NativeError::wire("wire section coverage overflow"))?;
    }
    if cursor != bytes.len() {
        return Err(NativeError::wire(
            "wire document contains unreferenced trailing bytes",
        ));
    }
    Ok(())
}

fn validate_section_records(
    bytes: &[u8],
    sections: &BTreeMap<SectionKind, Section>,
) -> NativeResult<()> {
    for section in sections.values() {
        let record_length = match section.kind {
            SectionKind::Metadata => Some(METADATA_LEN),
            SectionKind::Symbols => Some(SYMBOL_RECORD_LEN),
            SectionKind::Predicates => Some(PREDICATE_RECORD_LEN),
            SectionKind::Facts => Some(FACT_RECORD_LEN),
            SectionKind::Atoms => Some(ATOM_RECORD_LEN),
            SectionKind::Clauses => Some(CLAUSE_RECORD_LEN),
            SectionKind::Provenance => Some(PROVENANCE_RECORD_LEN),
            SectionKind::Strings
            | SectionKind::Config
            | SectionKind::Query
            | SectionKind::Delta
            | SectionKind::Result => None,
        };
        if let Some(record_length) = record_length {
            let expected = usize::try_from(section.count)
                .ok()
                .and_then(|count| count.checked_mul(record_length))
                .ok_or_else(|| NativeError::wire("wire record count overflow"))?;
            if expected != section.length {
                return Err(NativeError::wire(format!(
                    "wire {:?} count does not match its byte length",
                    section.kind
                )));
            }
        } else if section.kind == SectionKind::Strings {
            if usize::try_from(section.count).ok() != Some(section.length) {
                return Err(NativeError::wire(
                    "wire string byte count does not match its length",
                ));
            }
        } else if section.count != 1 {
            return Err(NativeError::wire(
                "single-payload wire section must declare count one",
            ));
        }
        if section.offset + section.length > bytes.len() {
            return Err(NativeError::wire(
                "validated wire section became unavailable",
            ));
        }
    }
    if let Some(metadata) = sections.get(&SectionKind::Metadata) {
        if metadata.count != 1 || metadata.length != METADATA_LEN {
            return Err(NativeError::wire(
                "wire metadata must contain exactly one fixed record",
            ));
        }
    }
    Ok(())
}

fn validate_cross_references(
    bytes: &[u8],
    sections: &BTreeMap<SectionKind, Section>,
) -> NativeResult<()> {
    let strings = section_slice(bytes, sections, SectionKind::Strings).unwrap_or(&[]);
    if std::str::from_utf8(strings).is_err() {
        return Err(NativeError::wire("wire string section is not valid UTF-8"));
    }
    if let Some(section) = sections.get(&SectionKind::Symbols) {
        for record in records(bytes, section, SYMBOL_RECORD_LEN)? {
            let kind = record[0];
            if kind > 7 || record[1] & !0b11 != 0 || read_u16(record, 2)? != 0 {
                return Err(NativeError::wire("wire symbol enum or flags are invalid"));
            }
            let offset = usize::try_from(read_u32(record, 4)?)
                .map_err(|_| NativeError::wire("wire string offset cannot fit this platform"))?;
            let length = usize::try_from(read_u32(record, 8)?)
                .map_err(|_| NativeError::wire("wire string length cannot fit this platform"))?;
            let end = offset
                .checked_add(length)
                .ok_or_else(|| NativeError::wire("wire string reference overflow"))?;
            if end > strings.len() || std::str::from_utf8(&strings[offset..end]).is_err() {
                return Err(NativeError::wire("wire symbol string reference is invalid"));
            }
        }
    }
    let symbol_count = sections
        .get(&SectionKind::Symbols)
        .map_or(0, |section| section.count);
    let mut arities = Vec::new();
    if let Some(section) = sections.get(&SectionKind::Predicates) {
        arities
            .try_reserve_exact(usize::try_from(section.count).unwrap_or(0))
            .map_err(|_| NativeError::wire("wire predicate validation allocation failed"))?;
        for record in records(bytes, section, PREDICATE_RECORD_LEN)? {
            let kind = record[0];
            let arity = record[1];
            if kind > 16 || !(1..=2).contains(&arity) {
                return Err(NativeError::wire("wire predicate kind or arity is invalid"));
            }
            if record[2] > 1 || (arity == 2 && record[3] > 1) || (arity == 1 && record[3] != 0xff) {
                return Err(NativeError::wire(
                    "wire predicate sort discriminant is invalid",
                ));
            }
            let symbol = read_u32(record, 4)?;
            if symbol != U32_NONE && symbol >= symbol_count {
                return Err(NativeError::wire(
                    "wire predicate references an unknown symbol",
                ));
            }
            arities.push(arity);
        }
    }
    let predicate_count = u32::try_from(arities.len())
        .map_err(|_| NativeError::wire("wire predicate count exceeds u32"))?;
    for kind in [SectionKind::Facts, SectionKind::Atoms] {
        if let Some(section) = sections.get(&kind) {
            for record in records(bytes, section, FACT_RECORD_LEN)? {
                let predicate = read_u32(record, 0)?;
                let arity = record[12];
                if predicate >= predicate_count
                    || usize::from(arity) > 2
                    || arity == 0
                    || arities[usize::try_from(predicate).unwrap_or(usize::MAX)] != arity
                {
                    return Err(NativeError::wire(
                        "wire atom/fact predicate or arity reference is invalid",
                    ));
                }
                if record[13] & !1 != 0 || read_u16(record, 14)? != 0 {
                    return Err(NativeError::wire("wire atom/fact flags are invalid"));
                }
                if arity == 1 && read_u32(record, 8)? != U32_NONE {
                    return Err(NativeError::wire(
                        "unary wire atom/fact must use the absent second argument sentinel",
                    ));
                }
            }
        }
    }
    if let Some(section) = sections.get(&SectionKind::Clauses) {
        let atom_count = sections
            .get(&SectionKind::Atoms)
            .map_or(0, |value| value.count);
        let provenance_count = sections
            .get(&SectionKind::Provenance)
            .map_or(0, |value| value.count);
        for record in records(bytes, section, CLAUSE_RECORD_LEN)? {
            validate_u32_range(
                read_u32(record, 0)?,
                read_u32(record, 4)?,
                atom_count,
                "body",
            )?;
            validate_u32_range(
                read_u32(record, 8)?,
                read_u32(record, 12)?,
                atom_count,
                "head",
            )?;
            if read_u32(record, 4)? == 0 && read_u32(record, 12)? == 0 {
                return Err(NativeError::wire(
                    "wire clause cannot have empty body and head",
                ));
            }
            validate_u32_range(
                read_u32(record, 16)?,
                read_u32(record, 20)?,
                provenance_count,
                "provenance",
            )?;
        }
    }
    Ok(())
}

fn validate_u32_range(offset: u32, count: u32, total: u32, name: &str) -> NativeResult<()> {
    let end = offset
        .checked_add(count)
        .ok_or_else(|| NativeError::wire(format!("wire {name} range overflow")))?;
    if end > total {
        return Err(NativeError::wire(format!(
            "wire {name} range references unavailable records"
        )));
    }
    Ok(())
}

fn records<'a>(
    bytes: &'a [u8],
    section: &Section,
    record_length: usize,
) -> NativeResult<impl Iterator<Item = &'a [u8]>> {
    let value = bytes
        .get(section.offset..section.offset + section.length)
        .ok_or_else(|| NativeError::wire("wire section became unavailable"))?;
    Ok(value.chunks_exact(record_length))
}

fn section_slice<'a>(
    bytes: &'a [u8],
    sections: &BTreeMap<SectionKind, Section>,
    kind: SectionKind,
) -> Option<&'a [u8]> {
    let section = sections.get(&kind)?;
    bytes.get(section.offset..section.offset + section.length)
}

fn parse_metadata(bytes: &[u8]) -> NativeResult<CoreMetadata> {
    if bytes.len() != METADATA_LEN {
        return Err(NativeError::wire("wire metadata length is invalid"));
    }
    Ok(CoreMetadata {
        ontology_fingerprint: read_array_32(bytes, 0)?,
        structural_fingerprint: read_array_32(bytes, 32)?,
        logical_fingerprint: read_array_32(bytes, 64)?,
        signature_fingerprint: read_array_32(bytes, 96)?,
        core_api_version: (read_u16(bytes, 128)?, read_u16(bytes, 130)?),
        core_model_schema_version: read_u32(bytes, 132)?,
        core_wire_format_version: (read_u16(bytes, 136)?, read_u16(bytes, 138)?),
        core_adapter_protocol_version: read_u32(bytes, 140)?,
    })
}

fn read_array_32(bytes: &[u8], offset: usize) -> NativeResult<[u8; 32]> {
    bytes
        .get(offset..offset + 32)
        .ok_or_else(|| NativeError::wire("wire 32-byte field is truncated"))?
        .try_into()
        .map_err(|_| NativeError::wire("wire 32-byte field has invalid length"))
}

fn read_u16(bytes: &[u8], offset: usize) -> NativeResult<u16> {
    let value: [u8; 2] = bytes
        .get(offset..offset + 2)
        .ok_or_else(|| NativeError::wire("wire u16 field is truncated"))?
        .try_into()
        .map_err(|_| NativeError::wire("wire u16 field has invalid length"))?;
    Ok(u16::from_le_bytes(value))
}

fn read_u32(bytes: &[u8], offset: usize) -> NativeResult<u32> {
    let value: [u8; 4] = bytes
        .get(offset..offset + 4)
        .ok_or_else(|| NativeError::wire("wire u32 field is truncated"))?
        .try_into()
        .map_err(|_| NativeError::wire("wire u32 field has invalid length"))?;
    Ok(u32::from_le_bytes(value))
}

fn read_u64(bytes: &[u8], offset: usize) -> NativeResult<u64> {
    let value: [u8; 8] = bytes
        .get(offset..offset + 8)
        .ok_or_else(|| NativeError::wire("wire u64 field is truncated"))?
        .try_into()
        .map_err(|_| NativeError::wire("wire u64 field has invalid length"))?;
    Ok(u64::from_le_bytes(value))
}

fn u64_to_usize(value: u64, name: &str) -> NativeResult<usize> {
    usize::try_from(value).map_err(|_| NativeError::wire(format!("wire {name} is too large")))
}

#[cfg(test)]
pub(crate) fn build_test_document(kind: DocumentKind, metadata: Option<&CoreMetadata>) -> Vec<u8> {
    let (section_kind, payload): (SectionKind, Vec<u8>) = if let Some(metadata) = metadata {
        let mut payload = Vec::with_capacity(METADATA_LEN);
        payload.extend_from_slice(&metadata.ontology_fingerprint);
        payload.extend_from_slice(&metadata.structural_fingerprint);
        payload.extend_from_slice(&metadata.logical_fingerprint);
        payload.extend_from_slice(&metadata.signature_fingerprint);
        payload.extend_from_slice(&metadata.core_api_version.0.to_le_bytes());
        payload.extend_from_slice(&metadata.core_api_version.1.to_le_bytes());
        payload.extend_from_slice(&metadata.core_model_schema_version.to_le_bytes());
        payload.extend_from_slice(&metadata.core_wire_format_version.0.to_le_bytes());
        payload.extend_from_slice(&metadata.core_wire_format_version.1.to_le_bytes());
        payload.extend_from_slice(&metadata.core_adapter_protocol_version.to_le_bytes());
        (SectionKind::Metadata, payload)
    } else {
        let section_kind = match kind {
            DocumentKind::Config => SectionKind::Config,
            DocumentKind::Query => SectionKind::Query,
            DocumentKind::Delta => SectionKind::Delta,
            DocumentKind::Result => SectionKind::Result,
            DocumentKind::Ontology => SectionKind::Metadata,
        };
        (
            section_kind,
            if kind == DocumentKind::Ontology {
                vec![0; METADATA_LEN]
            } else {
                Vec::new()
            },
        )
    };
    let payload_offset = HEADER_LEN + DIRECTORY_ENTRY_LEN;
    let padding = (8 - payload_offset % 8) % 8;
    let offset = payload_offset + padding;
    let mut bytes = vec![0; offset];
    bytes.extend_from_slice(&payload);
    let document_length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    bytes[..8].copy_from_slice(MAGIC);
    bytes[8..10].copy_from_slice(&IR_SCHEMA_VERSION.to_le_bytes());
    bytes[10..12].copy_from_slice(&(kind as u16).to_le_bytes());
    bytes[16..24].copy_from_slice(&document_length.to_le_bytes());
    bytes[24..32].copy_from_slice(&u64::try_from(HEADER_LEN).unwrap_or(u64::MAX).to_le_bytes());
    bytes[32..36].copy_from_slice(&1_u32.to_le_bytes());
    bytes[72..74].copy_from_slice(&(section_kind as u16).to_le_bytes());
    bytes[80..88].copy_from_slice(&u64::try_from(offset).unwrap_or(u64::MAX).to_le_bytes());
    bytes[88..96].copy_from_slice(
        &u64::try_from(payload.len())
            .unwrap_or(u64::MAX)
            .to_le_bytes(),
    );
    bytes[96..100].copy_from_slice(&1_u32.to_le_bytes());
    bytes[100..104].copy_from_slice(&8_u32.to_le_bytes());
    let hash = Sha256::digest(&bytes[HEADER_LEN..]);
    bytes[40..72].copy_from_slice(&hash);
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    const fn metadata() -> CoreMetadata {
        CoreMetadata {
            ontology_fingerprint: [1; 32],
            structural_fingerprint: [2; 32],
            logical_fingerprint: [3; 32],
            signature_fingerprint: [4; 32],
            core_api_version: (0, 1),
            core_model_schema_version: 1,
            core_wire_format_version: (1, 0),
            core_adapter_protocol_version: 1,
        }
    }

    #[test]
    fn validates_one_owned_metadata_copy() -> NativeResult<()> {
        let source = build_test_document(DocumentKind::Ontology, Some(&metadata()));
        let document = validate_owned(source, DocumentKind::Ontology)?;
        assert_eq!(document.metadata.as_ref(), Some(&metadata()));
        assert_eq!(
            document.bytes().len(),
            HEADER_LEN + DIRECTORY_ENTRY_LEN + METADATA_LEN
        );
        Ok(())
    }

    #[test]
    fn corrupt_lengths_offsets_hashes_and_versions_fail_without_panic() {
        let valid = build_test_document(DocumentKind::Ontology, Some(&metadata()));
        for offset in [0_usize, 8, 16, 24, 32, 40, 72, 80, 88, 96, 100] {
            let mut corrupt = valid.clone();
            corrupt[offset] ^= 0xff;
            assert!(validate_owned(corrupt, DocumentKind::Ontology).is_err());
        }
        for length in 0..HEADER_LEN {
            assert!(validate_owned(valid[..length].to_vec(), DocumentKind::Ontology).is_err());
        }
    }

    #[test]
    fn hostile_u64_and_count_metadata_never_allocate_from_claims() {
        let mut document = build_test_document(DocumentKind::Ontology, Some(&metadata()));
        document[16..24].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(validate_owned(document, DocumentKind::Ontology).is_err());

        let mut document = build_test_document(DocumentKind::Ontology, Some(&metadata()));
        document[32..36].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(validate_owned(document, DocumentKind::Ontology).is_err());
    }
}
