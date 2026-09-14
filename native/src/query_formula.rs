//! Bounded native clausification of assertion-local public query syntax.
// SPDX-License-Identifier: LGPL-3.0-or-later

use crate::error::{NativeError, NativeResult};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedGroundAtom, DecodedQuery, DecodedTerm, PredicateKind,
    SymbolKind, TermSort,
};
use crate::query_delta::{NativeQueryBase, QueryDeltaBuilder};
use crate::session::SessionQuery;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::sync::Arc;

pub(crate) const MAX_QUERY_BYTES: usize = 1024 * 1024;
pub(crate) const MAX_BATCH_BYTES: usize = 16 * MAX_QUERY_BYTES;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Identifier {
    base: Option<u32>,
    local: Option<u32>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Expression {
    Class {
        symbol: Identifier,
    },
    Not {
        value: Box<Self>,
    },
    And {
        values: Vec<Self>,
    },
    Or {
        values: Vec<Self>,
    },
    OneOf {
        individuals: Vec<Identifier>,
    },
    #[serde(rename = "self")]
    Self_ {
        role: u32,
    },
    All {
        role: u32,
        value: Box<Self>,
    },
    Some {
        role: u32,
        value: Box<Self>,
    },
    HasValue {
        role: u32,
        target: Identifier,
    },
    DataValue {
        role: u32,
        literal: u32,
    },
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Assertion {
    Class {
        expression: Expression,
        individual: Identifier,
    },
    Object {
        role: u32,
        source: Identifier,
        target: Identifier,
        negative: bool,
    },
    Data {
        role: u32,
        source: Identifier,
        literal: u32,
        negative: bool,
    },
    Same {
        individuals: Vec<Identifier>,
    },
    Different {
        individuals: Vec<Identifier>,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    schema: u32,
    permanent_program_sha256: String,
    axioms: Vec<Assertion>,
    individual_count: u32,
    class_count: u32,
}

struct Compiler {
    builder: QueryDeltaBuilder,
    individuals: u32,
    classes: u32,
    next_class: u32,
    steps: u32,
    cancellation: Arc<crate::cancel::CancellationState>,
}

fn ineligible(message: &'static str) -> NativeError {
    NativeError::feature(message).with_context("feature_id", "native_query_delta_ineligible")
}

fn resource(message: &'static str) -> NativeError {
    NativeError::new(crate::error::ErrorKind::Resource, "RESOURCE_LIMIT", message)
}

pub(crate) fn compile_request(
    base: Arc<NativeQueryBase>,
    bytes: &[u8],
    cancellation: Arc<crate::cancel::CancellationState>,
) -> NativeResult<SessionQuery<DecodedQuery>> {
    if bytes.len() > MAX_QUERY_BYTES {
        return Err(resource("native query exceeds byte bound"));
    }
    let request: Request = serde_json::from_slice(bytes)
        .map_err(|error| NativeError::wire(format!("invalid native query syntax: {error}")))?;
    if request.schema != 1
        || request.permanent_program_sha256
            != crate::model::hex(&base.ontology.metadata.program_sha256)
    {
        return Err(NativeError::wire(
            "native query schema or permanent owner differs",
        ));
    }
    if request.individual_count > 65_536
        || request.class_count > 65_536
        || request.axioms.is_empty()
        || request.axioms.len() > 4096
    {
        return Err(resource("native query local domain exceeds bound"));
    }
    let mut hash = Sha256::new();
    hash.update(b"pyhermit:native-query-delta:v1\0");
    hash.update(base.ontology.metadata.program_sha256);
    hash.update(bytes);
    let mut builder = QueryDeltaBuilder::new(base, hash.finalize().into());
    builder.delta.individual_count = builder
        .delta
        .individual_count
        .checked_add(request.individual_count)
        .ok_or_else(|| NativeError::wire("native query individual boundary overflows"))?;
    let next_class = builder.base.boundaries[SymbolKind::ClassExpression as usize]
        .checked_add(request.class_count)
        .ok_or_else(|| NativeError::wire("native query class boundary overflows"))?;
    let mut compiler = Compiler {
        builder,
        individuals: request.individual_count,
        classes: request.class_count,
        next_class,
        steps: 0,
        cancellation,
    };
    for axiom in &request.axioms {
        compiler.assertion(axiom)?;
    }
    Ok(compiler
        .builder
        .finish(vec!["native-assertion-delta".into()]))
}

impl Compiler {
    fn tick(&mut self) -> NativeResult<()> {
        self.steps = self
            .steps
            .checked_add(1)
            .ok_or_else(|| NativeError::wire("query work overflow"))?;
        if self.steps > 65_536 {
            return Err(NativeError::new(
                crate::error::ErrorKind::Resource,
                "RESOURCE_LIMIT",
                "native query local work exceeds its bound",
            )
            .with_context("limit", "native_query_work")
            .with_context("observed", self.steps.to_string())
            .with_context("allowed", "65536"));
        }
        if self.steps % 128 == 0 {
            self.cancellation.poll()?;
        }
        Ok(())
    }

    fn bound(&self, kind: SymbolKind, id: u32) -> NativeResult<u32> {
        if id >= self.builder.base.boundaries[kind as usize] {
            return Err(ineligible(
                "native query references an unknown retained symbol",
            ));
        }
        Ok(id)
    }

    fn object_role(&self, id: u32) -> NativeResult<u32> {
        self.bound(SymbolKind::ObjectRole, id)?;
        let program = &self.builder.base.ontology.program;
        let symbol = &program
            .domain(SymbolKind::ObjectRole)
            .ok_or_else(|| NativeError::wire("object-role domain absent"))?
            .values[id as usize];
        if !program.expressivity.inverse_roles
            && symbol.display.starts_with("inverse_object_property:")
        {
            return Err(ineligible(
                "query introduces inverse-role blocking requirements",
            ));
        }
        Ok(id)
    }

    fn identifier(
        &self,
        value: &Identifier,
        kind: SymbolKind,
        local_count: u32,
    ) -> NativeResult<u32> {
        match (value.base, value.local) {
            (Some(id), None) => self.bound(kind, id),
            (None, Some(id)) if id < local_count => self.builder.base.boundaries[kind as usize]
                .checked_add(id)
                .ok_or_else(|| NativeError::wire("native query symbol ID overflows")),
            _ => Err(NativeError::wire(
                "native query identifier must select exactly one valid domain",
            )),
        }
    }

    fn individual(&self, value: &Identifier) -> NativeResult<DecodedTerm> {
        Ok(DecodedTerm::Individual {
            individual_id: self.identifier(value, SymbolKind::Individual, self.individuals)?,
        })
    }

    fn literal(&self, id: u32) -> NativeResult<DecodedTerm> {
        self.bound(SymbolKind::SourceLiteral, id)?;
        let identity = self
            .builder
            .base
            .ontology
            .program
            .datatype_model
            .literal_identities
            .get(id as usize)
            .ok_or_else(|| ineligible("query requires an uncompiled literal payload"))?;
        if identity.source_literal_id != id {
            return Err(NativeError::wire("literal identity index differs"));
        }
        Ok(DecodedTerm::Data {
            source_literal_id: id,
            data_identity_id: identity.data_identity_id,
        })
    }

    fn atom(
        &mut self,
        kind: PredicateKind,
        symbol: Option<u32>,
        role: Option<u32>,
        mut arguments: Vec<DecodedTerm>,
    ) -> NativeResult<DecodedAtom> {
        self.tick()?;
        if matches!(
            kind,
            PredicateKind::DataRole | PredicateKind::NegatedDataRole
        ) {
            self.builder.predicate(
                PredicateKind::Inequality,
                None,
                None,
                &[TermSort::Data, TermSort::Data],
            )?;
        }
        if matches!(kind, PredicateKind::Equality | PredicateKind::Inequality) {
            arguments.sort();
        }
        let sorts = arguments
            .iter()
            .map(|term| match term {
                DecodedTerm::Variable { sort, .. } => *sort,
                DecodedTerm::Individual { .. } => TermSort::Object,
                DecodedTerm::Data { .. } => TermSort::Data,
            })
            .collect::<Vec<_>>();
        let predicate_id = self.builder.predicate(kind, symbol, role, &sorts)?;
        let opposite = match kind {
            PredicateKind::Concept => Some(PredicateKind::NegatedConcept),
            PredicateKind::NegatedConcept => Some(PredicateKind::Concept),
            PredicateKind::ObjectRole => Some(PredicateKind::NegatedObjectRole),
            PredicateKind::NegatedObjectRole => Some(PredicateKind::ObjectRole),
            PredicateKind::DataRole => Some(PredicateKind::NegatedDataRole),
            PredicateKind::NegatedDataRole => Some(PredicateKind::DataRole),
            PredicateKind::Equality => Some(PredicateKind::Inequality),
            PredicateKind::Inequality => Some(PredicateKind::Equality),
            _ => None,
        };
        if let Some(other_kind) = opposite {
            self.builder.predicate(other_kind, symbol, role, &sorts)?;
        }
        Ok(DecodedAtom {
            predicate_id,
            arguments,
        })
    }

    fn marker(&mut self, term: DecodedTerm) -> NativeResult<DecodedAtom> {
        let id = self.next_class;
        self.next_class = id
            .checked_add(1)
            .ok_or_else(|| NativeError::wire("query marker ID overflows"))?;
        self.atom(PredicateKind::Concept, Some(id), None, vec![term])
    }

    fn clause(
        &mut self,
        mut body: Vec<DecodedAtom>,
        mut head: Vec<DecodedAtom>,
    ) -> NativeResult<()> {
        self.tick()?;
        let mut stable = false;
        for _ in 0..130 {
            for atoms in [&mut body, &mut head] {
                let mut keyed = atoms
                    .drain(..)
                    .map(|atom| {
                        let key = crate::program_bridge::compile_atom(&atom)?.canonical_bytes();
                        Ok((key, atom))
                    })
                    .collect::<NativeResult<Vec<_>>>()?;
                keyed.sort_by(|left, right| left.0.cmp(&right.0));
                keyed.dedup_by(|left, right| left.0 == right.0);
                *atoms = keyed.into_iter().map(|(_, atom)| atom).collect();
            }
            let mut variables = std::collections::BTreeMap::new();
            let mut changed = false;
            for atom in body.iter_mut().chain(&mut head) {
                for term in &mut atom.arguments {
                    if let DecodedTerm::Variable { index, sort } = term {
                        let next = u32::try_from(variables.len())
                            .map_err(|_| NativeError::wire("query variable count overflows"))?;
                        let mapped = *variables.entry((*index, *sort)).or_insert(next);
                        changed |= mapped != *index;
                        *index = mapped;
                    }
                }
            }
            if !changed {
                stable = true;
                break;
            }
        }
        if !stable {
            return Err(ineligible(
                "query variable canonicalization exceeds bounded passes",
            ));
        }
        let join_order = (0..body.len())
            .map(|id| {
                u32::try_from(id).map_err(|_| NativeError::wire("query join ordinal overflows"))
            })
            .collect::<NativeResult<Vec<_>>>()?;
        self.builder.clause(DecodedClause {
            clause_id: 0,
            body,
            head,
            provenance_ids: Vec::new(),
            join_order,
        })
    }

    fn fact(&mut self, atom: DecodedAtom) {
        self.builder.delta.facts.push(DecodedGroundAtom {
            predicate_id: atom.predicate_id,
            arguments: atom.arguments,
            provenance_ids: vec![self.builder.base.provenance_id],
        });
    }

    fn formula(
        &mut self,
        expression: &Expression,
        negative: bool,
        term: DecodedTerm,
        depth: u32,
    ) -> NativeResult<DecodedAtom> {
        self.tick()?;
        if depth > 64 {
            return Err(resource("query syntax depth exceeds the supported bound"));
        }
        match expression {
            Expression::Not { value } => self.formula(value, !negative, term, depth + 1),
            Expression::Class { symbol } => {
                let id = self.identifier(symbol, SymbolKind::ClassExpression, self.classes)?;
                if symbol.base.is_some() {
                    let value = &self
                        .builder
                        .base
                        .ontology
                        .program
                        .domain(SymbolKind::ClassExpression)
                        .ok_or_else(|| NativeError::wire("class domain absent"))?
                        .values[id as usize];
                    let truth = match value.display.as_str() {
                        "class:http://www.w3.org/2002/07/owl#Thing" => Some(true),
                        "class:http://www.w3.org/2002/07/owl#Nothing" => Some(false),
                        _ => None,
                    };
                    if let Some(truth) = truth {
                        let marker = self.marker(term)?;
                        if truth == negative {
                            self.clause(vec![marker.clone()], Vec::new())?;
                        }
                        return Ok(marker);
                    }
                }
                self.atom(
                    if negative {
                        PredicateKind::NegatedConcept
                    } else {
                        PredicateKind::Concept
                    },
                    Some(id),
                    None,
                    vec![term],
                )
            }
            Expression::And { values } | Expression::Or { values } => {
                let conjunction = matches!(expression, Expression::And { .. }) != negative;
                let marker = self.marker(term.clone())?;
                let mut head = Vec::new();
                for value in values {
                    let atom = self.formula(value, negative, term.clone(), depth + 1)?;
                    if conjunction {
                        self.clause(vec![marker.clone()], vec![atom])?;
                    } else {
                        head.push(atom);
                    }
                }
                if !conjunction {
                    self.clause(vec![marker.clone()], head)?;
                }
                Ok(marker)
            }
            Expression::OneOf { individuals } => {
                let marker = self.marker(term.clone())?;
                let mut head = Vec::new();
                for individual in individuals {
                    let target = self.individual(individual)?;
                    let atom = self.atom(
                        if negative {
                            PredicateKind::Inequality
                        } else {
                            PredicateKind::Equality
                        },
                        None,
                        None,
                        vec![term.clone(), target],
                    )?;
                    if negative {
                        self.clause(vec![marker.clone()], vec![atom])?;
                    } else {
                        head.push(atom);
                    }
                }
                if !negative {
                    self.clause(vec![marker.clone()], head)?;
                }
                Ok(marker)
            }
            Expression::Self_ { role } => {
                self.object_role(*role)?;
                self.atom(
                    if negative {
                        PredicateKind::NegatedObjectRole
                    } else {
                        PredicateKind::ObjectRole
                    },
                    None,
                    Some(*role),
                    vec![term.clone(), term],
                )
            }
            Expression::HasValue { role, target } => {
                self.object_role(*role)?;
                let target = self.individual(target)?;
                self.atom(
                    if negative {
                        PredicateKind::NegatedObjectRole
                    } else {
                        PredicateKind::ObjectRole
                    },
                    None,
                    Some(*role),
                    vec![term, target],
                )
            }
            Expression::DataValue { role, literal } => {
                self.bound(SymbolKind::DataProperty, *role)?;
                let literal = self.literal(*literal)?;
                self.builder.delta.enable_datatypes = true;
                self.atom(
                    if negative {
                        PredicateKind::NegatedDataRole
                    } else {
                        PredicateKind::DataRole
                    },
                    None,
                    Some(*role),
                    vec![term, literal],
                )
            }
            Expression::All { role, value } | Expression::Some { role, value } => {
                self.object_role(*role)?;
                let universal = matches!(expression, Expression::All { .. }) != negative;
                let marker = self.marker(term.clone())?;
                if universal {
                    let index = depth
                        .checked_add(1)
                        .ok_or_else(|| NativeError::wire("query variable ID overflow"))?;
                    let target = DecodedTerm::Variable {
                        index,
                        sort: TermSort::Object,
                    };
                    let edge = self.atom(
                        PredicateKind::ObjectRole,
                        None,
                        Some(*role),
                        vec![term, target.clone()],
                    )?;
                    let filler = self.formula(value, negative, target, depth + 1)?;
                    self.clause(vec![marker.clone(), edge], vec![filler])?;
                } else {
                    if matches!(term, DecodedTerm::Variable { .. }) {
                        return Err(ineligible(
                            "nested existential query requires a fresh expansion template",
                        ));
                    }
                    let id = self.builder.individual()?;
                    let target = DecodedTerm::Individual { individual_id: id };
                    let edge = self.atom(
                        PredicateKind::ObjectRole,
                        None,
                        Some(*role),
                        vec![term, target.clone()],
                    )?;
                    let filler = self.formula(value, negative, target, depth + 1)?;
                    self.clause(vec![marker.clone()], vec![edge])?;
                    self.clause(vec![marker.clone()], vec![filler])?;
                }
                Ok(marker)
            }
        }
    }

    fn assertion(&mut self, assertion: &Assertion) -> NativeResult<()> {
        match assertion {
            Assertion::Class {
                expression,
                individual,
            } => {
                let term = self.individual(individual)?;
                let atom = self.formula(expression, false, term, 0)?;
                self.fact(atom);
            }
            Assertion::Object {
                role,
                source,
                target,
                negative,
            } => {
                self.object_role(*role)?;
                let terms = vec![self.individual(source)?, self.individual(target)?];
                let atom = self.atom(
                    if *negative {
                        PredicateKind::NegatedObjectRole
                    } else {
                        PredicateKind::ObjectRole
                    },
                    None,
                    Some(*role),
                    terms,
                )?;
                self.fact(atom);
            }
            Assertion::Data {
                role,
                source,
                literal,
                negative,
            } => {
                self.bound(SymbolKind::DataProperty, *role)?;
                let terms = vec![self.individual(source)?, self.literal(*literal)?];
                self.builder.delta.enable_datatypes = true;
                let atom = self.atom(
                    if *negative {
                        PredicateKind::NegatedDataRole
                    } else {
                        PredicateKind::DataRole
                    },
                    None,
                    Some(*role),
                    terms,
                )?;
                self.fact(atom);
            }
            Assertion::Same { individuals } | Assertion::Different { individuals } => {
                if individuals.len() < 2 {
                    return Err(NativeError::wire("equality query needs two individuals"));
                }
                let same = matches!(assertion, Assertion::Same { .. });
                for (index, source) in individuals.iter().enumerate() {
                    for target in individuals.iter().skip(index + 1) {
                        let terms = vec![self.individual(source)?, self.individual(target)?];
                        let atom = self.atom(
                            if same {
                                PredicateKind::Equality
                            } else {
                                PredicateKind::Inequality
                            },
                            None,
                            None,
                            terms,
                        )?;
                        self.fact(atom);
                    }
                    if same {
                        break;
                    }
                }
            }
        }
        Ok(())
    }
}
