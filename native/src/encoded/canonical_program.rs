//! Streaming serialization of the scalar `ClauseProgram` canonical-record contract.
//!
//! Record fields are deliberately emitted in lexicographic order to match Python's
//! compact `json.dumps(..., sort_keys=True, ensure_ascii=False)` byte stream.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::fmt;

use serde::ser::{SerializeSeq as _, SerializeStruct as _};
use serde::{Serialize, Serializer};

use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedDatatypeModel, DecodedExpressivity, DecodedGroundAtom,
    DecodedGroundDisjunction, DecodedLiteralIdentity, DecodedPredicate, DecodedProgram,
    DecodedProvenanceEntry, DecodedRoleAutomaton, DecodedRoleModel, DecodedRoleTransition,
    DecodedSymbolDomain, DecodedSymbolValue, DecodedTerm, PredicateKind, SymbolKind, TermSort,
};
use crate::model::IR_SCHEMA_VERSION;

pub(crate) struct CanonicalClauseProgram<'a>(pub(crate) &'a DecodedProgram);

trait CanonicalRecord {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer;
}

struct Record<'a, T>(&'a T);

impl<T> Serialize for Record<'_, T>
where
    T: CanonicalRecord,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize_canonical(serializer)
    }
}

struct Records<'a, T>(&'a [T]);

impl<T> Serialize for Records<'_, T>
where
    T: CanonicalRecord,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for value in self.0 {
            sequence.serialize_element(&Record(value))?;
        }
        sequence.end()
    }
}

struct HexValue<'a>(&'a [u8]);

impl fmt::Display for HexValue<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl Serialize for HexValue<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(self)
    }
}

struct HexDigests<'a>(&'a [[u8; 32]]);

impl Serialize for HexDigests<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for digest in self.0 {
            sequence.serialize_element(&HexValue(digest))?;
        }
        sequence.end()
    }
}

struct TermSorts<'a>(&'a [TermSort]);

impl Serialize for TermSorts<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for sort in self.0 {
            sequence.serialize_element(term_sort(*sort))?;
        }
        sequence.end()
    }
}

struct PredicateRegistry<'a>(&'a [DecodedPredicate]);

impl Serialize for PredicateRegistry<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("PredicateRegistry", 3)?;
        record.serialize_field("predicates", &Records(self.0))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "PredicateRegistry")?;
        record.end()
    }
}

struct ProvenanceTable<'a>(&'a [DecodedProvenanceEntry]);

impl Serialize for ProvenanceTable<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("ProvenanceTable", 3)?;
        record.serialize_field("entries", &Records(self.0))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "ProvenanceTable")?;
        record.end()
    }
}

struct SymbolTable<'a> {
    domains: &'a [DecodedSymbolDomain],
    predicates: &'a [DecodedPredicate],
}

impl Serialize for SymbolTable<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("SymbolTable", 4)?;
        record.serialize_field("domains", &Records(self.domains))?;
        record.serialize_field("predicates", &PredicateRegistry(self.predicates))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "SymbolTable")?;
        record.end()
    }
}

impl Serialize for CanonicalClauseProgram<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let program = self.0;
        let mut record = serializer.serialize_struct("ClauseProgram", 12)?;
        record.serialize_field("clauses", &Records(&program.clauses))?;
        record.serialize_field("datatype_model", &Record(&program.datatype_model))?;
        record.serialize_field("expressivity", &Record(&program.expressivity))?;
        record.serialize_field(
            "ground_disjunctions",
            &Records(&program.ground_disjunctions),
        )?;
        record.serialize_field("negative_facts", &Records(&program.negative_facts))?;
        record.serialize_field("positive_facts", &Records(&program.positive_facts))?;
        record.serialize_field("predicates", &PredicateRegistry(&program.predicates))?;
        record.serialize_field("provenance", &ProvenanceTable(&program.provenance))?;
        record.serialize_field("role_model", &Record(&program.role_model))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field(
            "symbols",
            &SymbolTable {
                domains: &program.symbol_domains,
                predicates: &program.predicates,
            },
        )?;
        record.serialize_field("type", "ClauseProgram")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedSymbolValue {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("SymbolValue", 7)?;
        record.serialize_field("display", &self.display)?;
        record.serialize_field("generated", &self.generated)?;
        record.serialize_field("identifier", &self.identifier)?;
        record.serialize_field("key_hex", &HexValue(&self.key))?;
        record.serialize_field("query_local", &self.query_local)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "SymbolValue")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedSymbolDomain {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("SymbolDomain", 4)?;
        record.serialize_field("kind", symbol_kind(self.kind))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "SymbolDomain")?;
        record.serialize_field("values", &Records(&self.values))?;
        record.end()
    }
}

impl CanonicalRecord for DecodedPredicate {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("Predicate", 11)?;
        record.serialize_field("annotation", &self.annotation)?;
        record.serialize_field("argument_sorts", &TermSorts(&self.argument_sorts))?;
        record.serialize_field("cardinality", &self.cardinality)?;
        record.serialize_field("filler_predicate_id", &self.filler_predicate_id)?;
        record.serialize_field("internal_key", &self.internal_key)?;
        record.serialize_field("kind", predicate_kind(self.kind))?;
        record.serialize_field("predicate_id", &self.predicate_id)?;
        record.serialize_field("role_id", &self.role_id)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("symbol_id", &self.symbol_id)?;
        record.serialize_field("type", "Predicate")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedTerm {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Self::Variable { index, sort } => {
                let mut record = serializer.serialize_struct("Variable", 4)?;
                record.serialize_field("index", index)?;
                record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
                record.serialize_field("sort", term_sort(*sort))?;
                record.serialize_field("type", "Variable")?;
                record.end()
            }
            Self::Individual { individual_id } => {
                let mut record = serializer.serialize_struct("IndividualTerm", 3)?;
                record.serialize_field("individual_id", individual_id)?;
                record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
                record.serialize_field("type", "IndividualTerm")?;
                record.end()
            }
            Self::Data {
                source_literal_id,
                data_identity_id,
            } => {
                let mut record = serializer.serialize_struct("DataConstant", 4)?;
                record.serialize_field("data_identity_id", data_identity_id)?;
                record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
                record.serialize_field("source_literal_id", source_literal_id)?;
                record.serialize_field("type", "DataConstant")?;
                record.end()
            }
        }
    }
}

impl CanonicalRecord for DecodedAtom {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("Atom", 4)?;
        record.serialize_field("arguments", &Records(&self.arguments))?;
        record.serialize_field("predicate_id", &self.predicate_id)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "Atom")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedGroundAtom {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("GroundAtom", 5)?;
        record.serialize_field("arguments", &Records(&self.arguments))?;
        record.serialize_field("predicate_id", &self.predicate_id)?;
        record.serialize_field("provenance_ids", &self.provenance_ids)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "GroundAtom")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedClause {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("DLClause", 7)?;
        record.serialize_field("body", &Records(&self.body))?;
        record.serialize_field("clause_id", &self.clause_id)?;
        record.serialize_field("head", &Records(&self.head))?;
        record.serialize_field("join_order", &self.join_order)?;
        record.serialize_field("provenance_ids", &self.provenance_ids)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "DLClause")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedGroundDisjunction {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("GroundDisjunctionIR", 5)?;
        record.serialize_field("disjuncts", &Records(&self.disjuncts))?;
        record.serialize_field("disjunction_id", &self.disjunction_id)?;
        record.serialize_field("provenance_ids", &self.provenance_ids)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "GroundDisjunctionIR")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedProvenanceEntry {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("ProvenanceEntry", 5)?;
        record.serialize_field("generated", &self.generated)?;
        record.serialize_field("provenance_id", &self.provenance_id)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("source_sha256", &HexDigests(&self.source_sha256))?;
        record.serialize_field("type", "ProvenanceEntry")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedRoleTransition {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("RoleTransitionIR", 5)?;
        record.serialize_field("role_id", &self.role_id)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("source_state", &self.source_state)?;
        record.serialize_field("target_state", &self.target_state)?;
        record.serialize_field("type", "RoleTransitionIR")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedRoleAutomaton {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("RoleAutomatonIR", 7)?;
        record.serialize_field("component_id", &self.component_id)?;
        record.serialize_field("final_states", &self.final_states)?;
        record.serialize_field("initial_state", &self.initial_state)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("state_count", &self.state_count)?;
        record.serialize_field("transitions", &Records(&self.transitions))?;
        record.serialize_field("type", "RoleAutomatonIR")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedRoleModel {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("RoleModelIR", 14)?;
        record.serialize_field("automata", &Records(&self.automata))?;
        record.serialize_field("bottom_data_property_id", &self.bottom_data_property_id)?;
        record.serialize_field("bottom_object_role_id", &self.bottom_object_role_id)?;
        record.serialize_field("complex_inclusions", &self.complex_inclusions)?;
        record.serialize_field("data_inclusions", &self.data_inclusions)?;
        record.serialize_field("data_property_count", &self.data_property_count)?;
        record.serialize_field("inverse_role_ids", &self.inverse_role_ids)?;
        record.serialize_field("non_simple_components", &self.non_simple_components)?;
        record.serialize_field("object_role_count", &self.object_role_count)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("simple_inclusions", &self.simple_inclusions)?;
        record.serialize_field("top_data_property_id", &self.top_data_property_id)?;
        record.serialize_field("top_object_role_id", &self.top_object_role_id)?;
        record.serialize_field("type", "RoleModelIR")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedLiteralIdentity {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("LiteralIdentityIR", 6)?;
        record.serialize_field("comparison_key", &self.comparison_key)?;
        record.serialize_field("data_identity_id", &self.data_identity_id)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("semantic_payload_json", &self.semantic_payload_json)?;
        record.serialize_field("source_literal_id", &self.source_literal_id)?;
        record.serialize_field("type", "LiteralIdentityIR")?;
        record.end()
    }
}

impl CanonicalRecord for DecodedDatatypeModel {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("DatatypeModelIR", 6)?;
        record.serialize_field("datatype_definitions", &self.datatype_definitions)?;
        record.serialize_field("literal_identities", &Records(&self.literal_identities))?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("semantic_payload_json", &self.semantic_payload_json)?;
        record.serialize_field("type", "DatatypeModelIR")?;
        record.serialize_field("unknown_datatype_ids", &self.unknown_datatype_ids)?;
        record.end()
    }
}

impl CanonicalRecord for DecodedExpressivity {
    fn serialize_canonical<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut record = serializer.serialize_struct("Expressivity", 12)?;
        record.serialize_field("abox", &self.abox)?;
        record.serialize_field("bottom_properties", &self.bottom_properties)?;
        record.serialize_field("complex_roles", &self.complex_roles)?;
        record.serialize_field("datatypes", &self.datatypes)?;
        record.serialize_field("inverse_roles", &self.inverse_roles)?;
        record.serialize_field("keys", &self.keys)?;
        record.serialize_field("nominals", &self.nominals)?;
        record.serialize_field("non_horn", &self.non_horn)?;
        record.serialize_field("number_restrictions", &self.number_restrictions)?;
        record.serialize_field("schema_version", &IR_SCHEMA_VERSION)?;
        record.serialize_field("type", "Expressivity")?;
        record.serialize_field("unknown_datatypes", &self.unknown_datatypes)?;
        record.end()
    }
}

const fn symbol_kind(kind: SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Entity => "entity",
        SymbolKind::ClassExpression => "class_expression",
        SymbolKind::DataRange => "data_range",
        SymbolKind::ObjectRole => "object_role",
        SymbolKind::DataProperty => "data_property",
        SymbolKind::Individual => "individual",
        SymbolKind::SourceLiteral => "source_literal",
        SymbolKind::DataValue => "data_value",
    }
}

const fn term_sort(sort: TermSort) -> &'static str {
    match sort {
        TermSort::Object => "object",
        TermSort::Data => "data",
    }
}

const fn predicate_kind(kind: PredicateKind) -> &'static str {
    match kind {
        PredicateKind::Concept => "concept",
        PredicateKind::NegatedConcept => "negated_concept",
        PredicateKind::Nominal => "nominal",
        PredicateKind::NegatedNominal => "negated_nominal",
        PredicateKind::ObjectRole => "object_role",
        PredicateKind::NegatedObjectRole => "negated_object_role",
        PredicateKind::DataRole => "data_role",
        PredicateKind::NegatedDataRole => "negated_data_role",
        PredicateKind::DataRange => "data_range",
        PredicateKind::NegatedDataRange => "negated_data_range",
        PredicateKind::Equality => "equality",
        PredicateKind::Inequality => "inequality",
        PredicateKind::AtLeastObject => "at_least_object",
        PredicateKind::AtLeastData => "at_least_data",
        PredicateKind::AnnotatedEquality => "annotated_equality",
        PredicateKind::AutomatonState => "automaton_state",
        PredicateKind::DisjointGuard => "disjoint_guard",
        PredicateKind::OrderingGuard => "ordering_guard",
        PredicateKind::NamedIndividual => "named_individual",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_terms_match_scalar_record_json_exactly() {
        let terms = [
            DecodedTerm::Variable {
                index: 3,
                sort: TermSort::Data,
            },
            DecodedTerm::Individual { individual_id: 5 },
            DecodedTerm::Data {
                source_literal_id: 7,
                data_identity_id: 11,
            },
        ];

        assert_eq!(
            serde_json::to_string(&Records(&terms)).unwrap(),
            concat!(
                r#"[{"index":3,"schema_version":1,"sort":"data","type":"Variable"},"#,
                r#"{"individual_id":5,"schema_version":1,"type":"IndividualTerm"},"#,
                r#"{"data_identity_id":11,"schema_version":1,"source_literal_id":7,"#,
                r#""type":"DataConstant"}]"#,
            ),
        );
    }

    #[test]
    fn canonical_symbol_value_streams_scalar_hex_and_key_order() {
        let value = DecodedSymbolValue {
            identifier: 2,
            key: vec![0, 15, 16, 255],
            display: "é".to_owned(),
            generated: true,
            query_local: false,
        };

        assert_eq!(
            serde_json::to_string(&Record(&value)).unwrap(),
            concat!(
                r#"{"display":"é","generated":true,"identifier":2,"key_hex":"000f10ff","#,
                r#""query_local":false,"schema_version":1,"type":"SymbolValue"}"#,
            ),
        );
    }
}
