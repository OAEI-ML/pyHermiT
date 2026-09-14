//! Compact public-domain context for the private encoded facade.
//!
//! The direct structural compiler owns the complete permanent program.  Python needs
//! only the source-visible ID/key pairs required to map coarse native results back to
//! pyowl-core values; exporting clauses, predicates, normalized records, or provenance
//! would recreate the ontology-sized shadow IR that WP18 removes.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::Serialize;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::input_wire::{DecodedOntology, DecodedSymbolValue, SymbolKind};

const SERVICE_CONTEXT_SCHEMA_VERSION: u16 = 3;
const MAX_SERVICE_CONTEXT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Serialize)]
struct ServiceContext {
    schema_version: u16,
    compiler_digest: String,
    permanent_program_sha256: String,
    deterministic_program: bool,
    semantic_equality_possible: bool,
    domains: Vec<ServiceDomain>,
}

#[derive(Serialize)]
struct ServiceDomain {
    kind: &'static str,
    values: Vec<ServiceSymbol>,
}

#[derive(Serialize)]
struct ServiceSymbol {
    identifier: u32,
    key_hex: String,
}

pub(crate) fn encode_service_context(
    ontology: &DecodedOntology,
    compiler_digest: &[u8; 32],
) -> NativeResult<Vec<u8>> {
    let named_individuals = ontology
        .named_individuals
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if named_individuals.len() != ontology.named_individuals.len() {
        return Err(NativeError::wire(
            "encoded service-context named-individual domain is not unique",
        ));
    }
    let program = &ontology.program;
    let domains = vec![
        service_domain(program, SymbolKind::Entity, "entity", |_value| true)?,
        service_domain(program, SymbolKind::ClassExpression, "class", |value| {
            value.display.starts_with("class:")
        })?,
        service_domain(
            program,
            SymbolKind::ObjectRole,
            "object_property",
            |value| {
                value.display.starts_with("object_property:")
                    || value.display.starts_with("inverse_object_property:")
            },
        )?,
        service_domain(
            program,
            SymbolKind::DataProperty,
            "data_property",
            |value| value.display.starts_with("data_property:"),
        )?,
        service_domain(program, SymbolKind::Individual, "individual", |value| {
            named_individuals.contains(&value.identifier)
        })?,
        service_domain(
            program,
            SymbolKind::SourceLiteral,
            "source_literal",
            |_value| true,
        )?,
    ];
    let expressivity = program.expressivity;
    let encoded = serde_json::to_vec(&ServiceContext {
        schema_version: SERVICE_CONTEXT_SCHEMA_VERSION,
        compiler_digest: crate::model::hex(compiler_digest),
        permanent_program_sha256: crate::model::hex(&ontology.metadata.program_sha256),
        deterministic_program: !expressivity.non_horn,
        semantic_equality_possible: expressivity.nominals
            || expressivity.number_restrictions
            || expressivity.keys,
        domains,
    })
    .map_err(|_| NativeError::invariant("encoded service-context serialization failed"))?;
    if encoded.len() > MAX_SERVICE_CONTEXT_BYTES {
        return Err(NativeError::new(
            ErrorKind::Resource,
            "RESOURCE_LIMIT",
            "encoded service context exceeds its byte limit",
        )
        .with_context("limit", "memory_bytes")
        .with_context("observed", encoded.len().to_string())
        .with_context("allowed", MAX_SERVICE_CONTEXT_BYTES.to_string()));
    }
    Ok(encoded)
}

fn service_domain(
    program: &crate::input_wire::DecodedProgram,
    kind: SymbolKind,
    label: &'static str,
    include: impl Fn(&DecodedSymbolValue) -> bool,
) -> NativeResult<ServiceDomain> {
    let domain = program
        .domain(kind)
        .ok_or_else(|| NativeError::wire("encoded service-context symbol domain is absent"))?;
    let values = domain
        .values
        .iter()
        .filter(|value| !value.generated && !value.query_local && include(value))
        .map(|value| ServiceSymbol {
            identifier: value.identifier,
            key_hex: crate::model::hex(&value.key),
        })
        .collect::<Vec<_>>();
    let identifiers = values
        .iter()
        .map(|value| value.identifier)
        .collect::<BTreeSet<_>>();
    let keys = values
        .iter()
        .map(|value| value.key_hex.as_str())
        .collect::<BTreeSet<_>>();
    if values
        .windows(2)
        .any(|pair| pair[0].identifier >= pair[1].identifier)
        || identifiers.len() != values.len()
        || keys.len() != values.len()
    {
        return Err(NativeError::wire(
            "encoded service-context public symbol domain is not canonical",
        ));
    }
    Ok(ServiceDomain {
        kind: label,
        values,
    })
}

/// One bounded, native-owned lookup index. Keys are validated once by the compiled
/// program and by this constructor; Python only asks for selected public objects.
pub(crate) struct ServiceSymbolIndex {
    ontology: Arc<DecodedOntology>,
    domains: BTreeMap<&'static str, SymbolDomainIndex>,
    pub(crate) estimated_bytes: u64,
}

struct SymbolDomainIndex {
    kind: SymbolKind,
    ids: Vec<u32>,
    by_key: BTreeMap<Vec<u8>, u32>,
}

impl ServiceSymbolIndex {
    pub(crate) fn new(
        ontology: Arc<DecodedOntology>,
        control: &crate::CancellationState,
    ) -> NativeResult<Self> {
        let named: BTreeSet<_> = ontology.named_individuals.iter().copied().collect();
        let mut domains = BTreeMap::new();
        let mut estimated_bytes = 0_u64;
        for (label, kind) in [
            ("entity", SymbolKind::Entity),
            ("class", SymbolKind::ClassExpression),
            ("object_property", SymbolKind::ObjectRole),
            ("data_property", SymbolKind::DataProperty),
            ("individual", SymbolKind::Individual),
            ("source_literal", SymbolKind::SourceLiteral),
        ] {
            let domain = ontology
                .program
                .domain(kind)
                .ok_or_else(|| NativeError::wire("service symbol domain is absent"))?;
            let mut ids = Vec::new();
            let mut by_key = BTreeMap::new();
            for value in &domain.values {
                control.poll()?;
                if value.generated
                    || value.query_local
                    || !match label {
                        "class" => value.display.starts_with("class:"),
                        "object_property" => {
                            value.display.starts_with("object_property:")
                                || value.display.starts_with("inverse_object_property:")
                        }
                        "data_property" => value.display.starts_with("data_property:"),
                        "individual" => named.contains(&value.identifier),
                        _ => true,
                    }
                {
                    continue;
                }
                estimated_bytes = estimated_bytes
                    .checked_add(
                        u64::try_from(value.key.len())
                            .unwrap_or(u64::MAX)
                            .saturating_add(128),
                    )
                    .ok_or_else(|| NativeError::invariant("native symbol index size overflow"))?;
                if estimated_bytes > MAX_SERVICE_CONTEXT_BYTES as u64 {
                    return Err(NativeError::new(
                        ErrorKind::Resource,
                        "RESOURCE_LIMIT",
                        "native symbol index exceeds its byte limit",
                    )
                    .with_context("limit", "native_symbol_index_bytes")
                    .with_context("observed", estimated_bytes.to_string())
                    .with_context("allowed", MAX_SERVICE_CONTEXT_BYTES.to_string()));
                }
                control.observe_memory(estimated_bytes);
                control.poll()?;
                if by_key.insert(value.key.clone(), value.identifier).is_some()
                    || ids
                        .last()
                        .is_some_and(|previous| *previous >= value.identifier)
                {
                    return Err(NativeError::wire(
                        "native service symbols are not canonical",
                    ));
                }
                ids.push(value.identifier);
            }
            domains.insert(label, SymbolDomainIndex { kind, ids, by_key });
        }
        Ok(Self {
            ontology,
            domains,
            estimated_bytes,
        })
    }

    fn domain(&self, label: &str) -> NativeResult<&SymbolDomainIndex> {
        self.domains
            .get(label)
            .ok_or_else(|| NativeError::wire("unknown native symbol domain"))
    }

    pub(crate) fn count(&self, label: &str) -> NativeResult<usize> {
        Ok(self.domain(label)?.ids.len())
    }

    pub(crate) fn ids(&self, label: &str) -> NativeResult<Vec<u32>> {
        Ok(self.domain(label)?.ids.clone())
    }

    pub(crate) fn id_at(&self, label: &str, offset: usize) -> NativeResult<Option<u32>> {
        Ok(self.domain(label)?.ids.get(offset).copied())
    }

    pub(crate) fn find(&self, label: &str, key: &[u8]) -> NativeResult<Option<u32>> {
        Ok(self.domain(label)?.by_key.get(key).copied())
    }

    pub(crate) fn key(&self, label: &str, id: u32) -> NativeResult<Option<&[u8]>> {
        let selected = self.domain(label)?;
        if selected.ids.binary_search(&id).is_err() {
            return Ok(None);
        }
        let domain = self
            .ontology
            .program
            .domain(selected.kind)
            .ok_or_else(|| NativeError::invariant("native symbol domain disappeared"))?;
        let value = domain
            .values
            .get(
                usize::try_from(id)
                    .map_err(|_| NativeError::wire("symbol ID exceeds platform size"))?,
            )
            .ok_or_else(|| NativeError::invariant("native symbol ID is dangling"))?;
        Ok(Some(&value.key))
    }
}
