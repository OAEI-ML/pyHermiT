//! Native-only, assertion-local query reductions over an immutable permanent program.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::error::{NativeError, NativeResult};
use crate::input_wire::{
    DecodedClause, DecodedOntology, DecodedPredicate, DecodedProvenanceEntry, DecodedQuery,
    NativeQueryDelta, PredicateKind, SymbolKind, TermSort,
};
use crate::session::{QueryKey, SessionQuery};

type PredicateIdentity = (u16, Option<u32>, Option<u32>, Vec<TermSort>);

/// Index once per permanent program. Query builders only inspect their requested symbols.
#[derive(Debug)]
pub(crate) struct NativeQueryBase {
    pub ontology: Arc<DecodedOntology>,
    pub boundaries: [u32; 8],
    pub predicate_count: u32,
    pub clause_count: u32,
    pub provenance_id: u32,
    individual_keys: BTreeMap<Vec<u8>, u32>,
    predicates: BTreeMap<PredicateIdentity, u32>,
}

impl NativeQueryBase {
    pub fn new(ontology: Arc<DecodedOntology>) -> NativeResult<Arc<Self>> {
        let mut boundaries = [0; 8];
        for domain in &ontology.program.symbol_domains {
            boundaries[domain.kind as usize] = u32::try_from(domain.values.len())
                .map_err(|_| NativeError::wire("native query symbol boundary exceeds u32"))?;
        }
        let mut predicates = BTreeMap::new();
        for predicate in &ontology.program.predicates {
            // Specialized cardinality/internal predicates are never requested by this API.
            if predicate.cardinality.is_some()
                || predicate.filler_predicate_id.is_some()
                || !predicate.annotation.is_empty()
                || predicate.internal_key.is_some()
            {
                continue;
            }
            let key = (
                predicate.kind as u16,
                predicate.symbol_id,
                predicate.role_id,
                predicate.argument_sorts.clone(),
            );
            if predicates.insert(key, predicate.predicate_id).is_some() {
                return Err(NativeError::wire(
                    "native query predicate identity is duplicated",
                ));
            }
        }
        let mut individual_keys = BTreeMap::new();
        if let Some(domain) = ontology.program.domain(SymbolKind::Individual) {
            for value in &domain.values {
                if individual_keys
                    .insert(value.key.clone(), value.identifier)
                    .is_some()
                {
                    return Err(NativeError::wire("query individual identity is duplicated"));
                }
            }
        }
        Ok(Arc::new(Self {
            individual_keys,
            predicate_count: u32::try_from(ontology.program.predicates.len())
                .map_err(|_| NativeError::wire("native query predicate boundary exceeds u32"))?,
            clause_count: u32::try_from(ontology.program.clauses.len())
                .map_err(|_| NativeError::wire("native query clause boundary exceeds u32"))?,
            provenance_id: u32::try_from(ontology.program.provenance.len())
                .map_err(|_| NativeError::wire("native query provenance boundary exceeds u32"))?,
            ontology,
            boundaries,
            predicates,
        }))
    }

    pub fn find_individual(&self, key: &[u8]) -> Option<u32> {
        self.individual_keys.get(key).copied()
    }

    pub fn find(
        &self,
        kind: PredicateKind,
        symbol_id: Option<u32>,
        role_id: Option<u32>,
        sorts: &[TermSort],
    ) -> Option<u32> {
        self.predicates
            .get(&(kind as u16, symbol_id, role_id, sorts.to_vec()))
            .copied()
    }
}

pub(crate) struct QueryDeltaBuilder {
    pub base: Arc<NativeQueryBase>,
    pub delta: NativeQueryDelta,
    query_hash: [u8; 32],
}

impl QueryDeltaBuilder {
    pub fn new(base: Arc<NativeQueryBase>, query_hash: [u8; 32]) -> Self {
        let delta = NativeQueryDelta {
            provenance: DecodedProvenanceEntry {
                provenance_id: base.provenance_id,
                source_sha256: vec![query_hash],
                generated: true,
            },
            predicates: Vec::new(),
            clauses: Vec::new(),
            facts: Vec::new(),
            disjunctions: Vec::new(),
            individual_count: base.boundaries[SymbolKind::Individual as usize],
            data_count: base.boundaries[SymbolKind::DataValue as usize],
            enable_datatypes: false,
        };
        Self {
            base,
            delta,
            query_hash,
        }
    }

    pub fn individual(&mut self) -> NativeResult<u32> {
        let id = self.delta.individual_count;
        self.delta.individual_count = id
            .checked_add(1)
            .ok_or_else(|| NativeError::wire("native query individual ID exceeds u32"))?;
        Ok(id)
    }

    pub fn data(&mut self) -> NativeResult<u32> {
        let id = self.delta.data_count;
        self.delta.data_count = id
            .checked_add(1)
            .ok_or_else(|| NativeError::wire("native query data ID exceeds u32"))?;
        self.delta.enable_datatypes = true;
        self.predicate(
            PredicateKind::Inequality,
            None,
            None,
            &[TermSort::Data, TermSort::Data],
        )?;
        Ok(id)
    }

    pub fn predicate(
        &mut self,
        kind: PredicateKind,
        symbol_id: Option<u32>,
        role_id: Option<u32>,
        sorts: &[TermSort],
    ) -> NativeResult<u32> {
        if let Some(id) = self.base.find(kind, symbol_id, role_id, sorts) {
            return Ok(id);
        }
        if let Some(predicate) = self.delta.predicates.iter().find(|p| {
            p.kind == kind
                && p.symbol_id == symbol_id
                && p.role_id == role_id
                && p.argument_sorts == sorts
        }) {
            return Ok(predicate.predicate_id);
        }
        let predicate_id = self
            .base
            .predicate_count
            .checked_add(
                u32::try_from(self.delta.predicates.len())
                    .map_err(|_| NativeError::wire("native local predicates exceed u32"))?,
            )
            .ok_or_else(|| NativeError::wire("native local predicate ID exceeds u32"))?;
        self.delta.predicates.push(DecodedPredicate {
            predicate_id,
            kind,
            argument_sorts: sorts.to_vec(),
            symbol_id,
            role_id,
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        });
        Ok(predicate_id)
    }

    pub fn clause(&mut self, mut clause: DecodedClause) -> NativeResult<()> {
        clause.clause_id = self
            .base
            .clause_count
            .checked_add(
                u32::try_from(self.delta.clauses.len())
                    .map_err(|_| NativeError::wire("native local clauses exceed u32"))?,
            )
            .ok_or_else(|| NativeError::wire("native local clause ID exceeds u32"))?;
        clause.provenance_ids = vec![self.base.provenance_id];
        self.delta.clauses.push(clause);
        Ok(())
    }

    pub fn finish(self, interpretation: Vec<String>) -> SessionQuery<DecodedQuery> {
        let query = DecodedQuery {
            permanent_program_sha256: self.base.ontology.metadata.program_sha256,
            query_hash: self.query_hash,
            overlay_program_sha256: Some(self.query_hash),
            first_local_predicate_id: self.base.predicate_count,
            first_local_symbols: self.base.boundaries,
            requires_rebuild: false,
            program: None,
            native_delta: Some(self.delta),
            reason: None,
            interpretation,
        };
        SessionQuery::new(QueryKey::new(self.query_hash), query)
    }
}
