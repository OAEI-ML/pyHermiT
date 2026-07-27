//! Compact public-domain context for the private encoded facade.
//!
//! The direct structural compiler owns the complete permanent program.  Python needs
//! only the source-visible ID/key pairs required to map coarse native results back to
//! pyowl-core values; exporting clauses, predicates, normalized records, or provenance
//! would recreate the ontology-sized shadow IR that WP18 removes.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

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
