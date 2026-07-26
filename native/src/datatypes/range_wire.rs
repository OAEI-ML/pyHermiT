//! Canonical datatype semantic-model wire decoder and exact mixed-domain ranges.
//!
//! The Python compiler has already validated lexical forms and serialized exact
//! identities/comparisons.  This module validates that canonical JSON vocabulary,
//! reconstructs semantic values without lexical reparsing, validates named datatype
//! graphs, and compiles supported roots into a bounded DNF over disjoint data-value
//! families.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

use super::range::{
    BinaryRange, BooleanRange, Cardinality, IEEERange, LengthFacet, NumericDomain, NumericRange,
    OrderedFacet, RangeLimits,
};
use super::value::{
    decode_literal_semantic, BinaryKind, ComparisonValue, DataIdentity, DatatypeControl,
    DatatypeError, DatatypeLimits, DecodedLiteral, ExactRational, IEEEFormat,
};
use super::xsd_regex::{RegexLimits, XsdRegex};

const SCHEMA_VERSION: u32 = 1;
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const RDFS_LITERAL: &str = "http://www.w3.org/2000/01/rdf-schema#Literal";
const OWL_REAL: &str = "http://www.w3.org/2002/07/owl#real";
const OWL_RATIONAL: &str = "http://www.w3.org/2002/07/owl#rational";

const XSD_BOOLEAN: &str = "http://www.w3.org/2001/XMLSchema#boolean";
const XSD_DECIMAL: &str = "http://www.w3.org/2001/XMLSchema#decimal";
const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
const XSD_FLOAT: &str = "http://www.w3.org/2001/XMLSchema#float";
const XSD_DOUBLE: &str = "http://www.w3.org/2001/XMLSchema#double";
const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";
const XSD_NORMALIZED_STRING: &str = "http://www.w3.org/2001/XMLSchema#normalizedString";
const XSD_TOKEN: &str = "http://www.w3.org/2001/XMLSchema#token";
const XSD_LANGUAGE: &str = "http://www.w3.org/2001/XMLSchema#language";
const XSD_NAME: &str = "http://www.w3.org/2001/XMLSchema#Name";
const XSD_NCNAME: &str = "http://www.w3.org/2001/XMLSchema#NCName";
const XSD_NMTOKEN: &str = "http://www.w3.org/2001/XMLSchema#NMTOKEN";
const XSD_HEX_BINARY: &str = "http://www.w3.org/2001/XMLSchema#hexBinary";
const XSD_BASE64_BINARY: &str = "http://www.w3.org/2001/XMLSchema#base64Binary";
const XSD_ANY_URI: &str = "http://www.w3.org/2001/XMLSchema#anyURI";
const XSD_DATE_TIME: &str = "http://www.w3.org/2001/XMLSchema#dateTime";
const XSD_DATE_TIME_STAMP: &str = "http://www.w3.org/2001/XMLSchema#dateTimeStamp";
const RDF_PLAIN_LITERAL: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const RDF_XML_LITERAL: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";

const XSD_MIN_INCLUSIVE: &str = "http://www.w3.org/2001/XMLSchema#minInclusive";
const XSD_MIN_EXCLUSIVE: &str = "http://www.w3.org/2001/XMLSchema#minExclusive";
const XSD_MAX_INCLUSIVE: &str = "http://www.w3.org/2001/XMLSchema#maxInclusive";
const XSD_MAX_EXCLUSIVE: &str = "http://www.w3.org/2001/XMLSchema#maxExclusive";
const XSD_LENGTH: &str = "http://www.w3.org/2001/XMLSchema#length";
const XSD_MIN_LENGTH: &str = "http://www.w3.org/2001/XMLSchema#minLength";
const XSD_MAX_LENGTH: &str = "http://www.w3.org/2001/XMLSchema#maxLength";
const XSD_PATTERN: &str = "http://www.w3.org/2001/XMLSchema#pattern";
const RDF_LANG_RANGE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange";

/// Resource controls for canonical model decoding and mixed-domain compilation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RangeWireLimits {
    pub max_payload_bytes: u64,
    pub max_json_nesting: u64,
    pub max_data_range_depth: u64,
    pub max_data_range_nodes: u64,
    pub max_definitions: u64,
    pub max_dnf_clauses: u64,
    pub cancellation_poll_stride: u64,
    pub values: DatatypeLimits,
    pub ranges: RangeLimits,
    pub regex: RegexLimits,
}

impl Default for RangeWireLimits {
    fn default() -> Self {
        Self {
            max_payload_bytes: 16_000_000,
            // Stay below serde_json's defensive recursion ceiling while leaving
            // room for model, facet, and literal-record containers around the
            // semantic data-range tree.
            max_json_nesting: 120,
            // Recursive serde decoding has a fixed defensive recursion ceiling. A
            // smaller explicit semantic ceiling turns that into a typed resource error.
            max_data_range_depth: 64,
            max_data_range_nodes: 100_000,
            max_definitions: 100_000,
            max_dnf_clauses: 100_000,
            cancellation_poll_stride: 64,
            values: DatatypeLimits::default(),
            ranges: RangeLimits::default(),
            regex: RegexLimits::default(),
        }
    }
}

impl RangeWireLimits {
    fn validate(self) -> Result<Self, DatatypeError> {
        let values = [
            ("max_payload_bytes", self.max_payload_bytes),
            ("max_json_nesting", self.max_json_nesting),
            ("max_data_range_depth", self.max_data_range_depth),
            ("max_data_range_nodes", self.max_data_range_nodes),
            ("max_definitions", self.max_definitions),
            ("max_dnf_clauses", self.max_dnf_clauses),
            ("cancellation_poll_stride", self.cancellation_poll_stride),
        ];
        if let Some((name, _)) = values.into_iter().find(|(_, value)| *value == 0) {
            return Err(DatatypeError::invalid(format!(
                "native data-range wire limit must be positive: {name}"
            )));
        }
        Ok(self)
    }
}

/// Policy for canonical `opaque` atoms emitted by the Python compatibility layer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpaqueRangePolicy {
    Reject,
    Preserve,
}

/// One decoded, graph-validated datatype semantic model.
#[derive(Clone, Debug)]
pub struct NativeDatatypeRangeModel {
    data_ranges: Vec<RangeExpression>,
    definitions: BTreeMap<String, RangeExpression>,
    opaque_range_ids: Vec<u32>,
    limits: RangeWireLimits,
}

impl NativeDatatypeRangeModel {
    #[must_use]
    pub fn range_count(&self) -> usize {
        self.data_ranges.len()
    }

    #[must_use]
    pub fn definition_count(&self) -> usize {
        self.definitions.len()
    }

    #[must_use]
    pub fn opaque_range_ids(&self) -> &[u32] {
        &self.opaque_range_ids
    }

    pub fn compile_range(
        &self,
        data_range_id: u32,
        control: &impl DatatypeControl,
    ) -> Result<NativeDataRange, DatatypeError> {
        let index = usize::try_from(data_range_id)
            .map_err(|_| DatatypeError::invalid("data-range ID is not representable"))?;
        let expression = self
            .data_ranges
            .get(index)
            .ok_or_else(|| DatatypeError::invalid("data-range ID is dangling"))?;
        let mut compiler = DnfCompiler::new(&self.definitions, self.limits, control);
        let clauses = compiler.compile(expression, false, 1)?;
        Ok(NativeDataRange { clauses })
    }
}

/// Exact mixed-family DNF compiled from a canonical semantic expression.
#[derive(Clone, Debug)]
pub struct NativeDataRange {
    clauses: Dnf,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NativeSymbolicDataWitness {
    pub family: NativeDataValueFamily,
    pub domain_digest: [u8; 32],
    pub ordinal: u64,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NativeDataWitness {
    Concrete(DataIdentity),
    Symbolic(NativeSymbolicDataWitness),
}

impl NativeDataRange {
    #[must_use]
    pub fn all() -> Self {
        Self {
            clauses: vec![Vec::new()],
        }
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    pub fn contains(
        &self,
        value: &DataIdentity,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        let limits = limits.validate()?;
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            let mut retained = true;
            for atom in clause {
                if atom.atom.contains(value, limits, control)? != atom.positive {
                    retained = false;
                    break;
                }
            }
            if retained {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn is_empty_exact(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        let limits = limits.validate()?;
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            if clause_nonempty(clause, limits, control)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn intersection(
        &self,
        other: &Self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Self, DatatypeError> {
        let limits = limits.validate()?;
        Ok(Self {
            clauses: and_dnf(&self.clauses, &other.clauses, limits, control)?,
        })
    }

    pub fn complement(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Self, DatatypeError> {
        let limits = limits.validate()?;
        Ok(Self {
            clauses: not_dnf(&self.clauses, limits, control)?,
        })
    }

    pub fn cardinality_at_least(
        &self,
        minimum: u64,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        if minimum == 0 {
            return Ok(true);
        }
        let limits = limits.validate()?;
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            if clause_cardinality_up_to(clause, minimum, limits, control)? == minimum {
                return Ok(true);
            }
        }
        if minimum > limits.ranges.max_enumeration_values {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                minimum,
                limits.ranges.max_enumeration_values,
            ));
        }
        let mut identities = BTreeSet::new();
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            identities.extend(enumerate_clause(clause, limits, control)?);
            if u64::try_from(identities.len()).unwrap_or(u64::MAX) >= minimum {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn witness(
        &self,
        excluding: &BTreeSet<NativeDataWitness>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<NativeDataWitness, DatatypeError> {
        let limits = limits.validate()?;
        control.observe_memory(
            u64::try_from(excluding.len())
                .unwrap_or(u64::MAX)
                .saturating_mul(48),
        )?;
        let concrete: BTreeSet<_> = excluding
            .iter()
            .filter_map(|value| match value {
                NativeDataWitness::Concrete(identity) => Some(identity.clone()),
                NativeDataWitness::Symbolic(_) => None,
            })
            .collect();
        let digest = dnf_digest(&self.clauses);
        for (clause_index, clause) in self.clauses.iter().enumerate() {
            poll_index(clause_index, limits, control)?;
            if let Some(values) = explicit_candidates(clause, limits, control)? {
                if let Some(value) = values.into_iter().find(|value| !concrete.contains(value)) {
                    return Ok(NativeDataWitness::Concrete(value));
                }
                continue;
            }
            for subset in clause_family_subsets(clause, limits, control)? {
                if let Some(value) = subset.first_identity(&concrete, limits, control)? {
                    return Ok(NativeDataWitness::Concrete(value));
                }
                let family_exclusions = concrete
                    .iter()
                    .filter(|value| identity_family(value) == subset.family)
                    .count();
                let required = u64::try_from(family_exclusions)
                    .unwrap_or(u64::MAX)
                    .saturating_add(1);
                if subset.cardinality_up_to(required, limits, control)? == required {
                    let used: BTreeSet<_> = excluding
                        .iter()
                        .filter_map(|value| match value {
                            NativeDataWitness::Symbolic(symbolic)
                                if symbolic.family == subset.family
                                    && symbolic.domain_digest == digest =>
                            {
                                Some(symbolic.ordinal)
                            }
                            _ => None,
                        })
                        .collect();
                    let mut ordinal = 0_u64;
                    while used.contains(&ordinal) {
                        if ordinal >= limits.ranges.max_witness_steps {
                            return Err(DatatypeError::resource(
                                "max_witness_steps",
                                ordinal.saturating_add(1),
                                limits.ranges.max_witness_steps,
                            ));
                        }
                        ordinal = ordinal.saturating_add(1);
                        poll_index(
                            usize::try_from(ordinal).unwrap_or(usize::MAX),
                            limits,
                            control,
                        )?;
                    }
                    return Ok(NativeDataWitness::Symbolic(NativeSymbolicDataWitness {
                        family: subset.family,
                        domain_digest: digest,
                        ordinal,
                    }));
                }
            }
        }
        Err(DatatypeError::invalid(
            "data range has no nonexcluded witness",
        ))
    }

    pub fn cardinality(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Cardinality, DatatypeError> {
        let limits = limits.validate()?;
        let mut clause_counts = Vec::new();
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            let cardinality = clause_cardinality(clause, limits, control)?;
            if cardinality == Cardinality::Infinite {
                return Ok(Cardinality::Infinite);
            }
            clause_counts.push(cardinality);
        }
        if clause_counts.is_empty() {
            return Ok(Cardinality::Empty);
        }
        if clause_counts.len() == 1 {
            return Ok(clause_counts.remove(0));
        }
        let mut upper = BigUint::zero();
        for value in clause_counts {
            if let Cardinality::Finite(value) = value {
                upper += value;
            }
        }
        if upper > BigUint::from(limits.ranges.max_enumeration_values) {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                limits.ranges.max_enumeration_values.saturating_add(1),
                limits.ranges.max_enumeration_values,
            ));
        }
        let identities = self.enumerate_identities(limits, control)?;
        Ok(cardinality_from_count(BigUint::from(identities.len())))
    }

    pub fn enumerate_identities(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        let limits = limits.validate()?;
        let mut identities = BTreeSet::new();
        for (index, clause) in self.clauses.iter().enumerate() {
            poll_index(index, limits, control)?;
            identities.extend(enumerate_clause(clause, limits, control)?);
            let observed = u64::try_from(identities.len()).unwrap_or(u64::MAX);
            if observed > limits.ranges.max_enumeration_values {
                return Err(DatatypeError::resource(
                    "max_enumeration_values",
                    observed,
                    limits.ranges.max_enumeration_values,
                ));
            }
        }
        Ok(identities.into_iter().collect())
    }
}

/// Decode a complete canonical `DatatypeSemanticModelPayload` record.
pub fn decode_datatype_range_model(
    bytes: &[u8],
    limits: RangeWireLimits,
    opaque_policy: OpaqueRangePolicy,
    control: &impl DatatypeControl,
) -> Result<NativeDatatypeRangeModel, DatatypeError> {
    let limits = limits.validate()?;
    preflight_bytes(bytes, limits, control)?;
    let wire: ModelWire = serde_json::from_slice(bytes)?;
    require_canonical(bytes, &wire)?;
    if wire.record != "datatype_semantic_model" || wire.schema_version != SCHEMA_VERSION {
        return Err(DatatypeError::invalid(
            "unsupported datatype semantic model record or schema version",
        ));
    }
    let definition_count = u64::try_from(wire.definitions.len()).unwrap_or(u64::MAX);
    if definition_count > limits.max_definitions {
        return Err(DatatypeError::resource(
            "max_definitions",
            definition_count,
            limits.max_definitions,
        ));
    }
    let mut context = DecodeContext::new(limits, opaque_policy, control);
    let mut definitions = BTreeMap::new();
    let mut previous_name: Option<&str> = None;
    for definition in &wire.definitions {
        context.poll()?;
        if definition.record != "datatype_definition_semantic"
            || definition.schema_version != SCHEMA_VERSION
        {
            return Err(DatatypeError::invalid(
                "unsupported datatype definition record or schema version",
            ));
        }
        validate_iri(&definition.datatype_iri)?;
        if is_supported_datatype(&definition.datatype_iri) {
            return Err(DatatypeError::invalid(
                "built-in OWL datatypes cannot be redefined",
            ));
        }
        if previous_name.is_some_and(|name| name >= definition.datatype_iri.as_str()) {
            return Err(DatatypeError::invalid(
                "datatype definitions are not strictly sorted and unique",
            ));
        }
        previous_name = Some(&definition.datatype_iri);
        definitions.insert(
            definition.datatype_iri.clone(),
            context.decode_range(&definition.data_range, 1)?,
        );
    }
    let mut data_ranges = Vec::new();
    let mut opaque_range_ids = Vec::new();
    for (index, value) in wire.data_ranges.iter().enumerate() {
        let expression = context.decode_range(value, 1)?;
        if expression.contains_opaque() {
            opaque_range_ids.push(u32::try_from(index).map_err(|_| {
                DatatypeError::resource(
                    "max_data_range_nodes",
                    u64::MAX,
                    limits.max_data_range_nodes,
                )
            })?);
        }
        data_ranges.push(expression);
    }
    validate_definition_graph(&data_ranges, &definitions, limits, control)?;
    control.poll()?;
    Ok(NativeDatatypeRangeModel {
        data_ranges,
        definitions,
        opaque_range_ids,
        limits,
    })
}

/// Decode one standalone canonical `DataRangeSemanticPayload` record.
pub fn decode_data_range_semantic(
    bytes: &[u8],
    limits: RangeWireLimits,
    opaque_policy: OpaqueRangePolicy,
    control: &impl DatatypeControl,
) -> Result<NativeDataRange, DatatypeError> {
    let limits = limits.validate()?;
    preflight_bytes(bytes, limits, control)?;
    let wire: RangeWire = serde_json::from_slice(bytes)?;
    require_canonical(bytes, &wire)?;
    let mut context = DecodeContext::new(limits, opaque_policy, control);
    let expression = context.decode_range(&wire, 1)?;
    validate_definition_graph(
        std::slice::from_ref(&expression),
        &BTreeMap::new(),
        limits,
        control,
    )?;
    let definitions = BTreeMap::new();
    let mut compiler = DnfCompiler::new(&definitions, limits, control);
    Ok(NativeDataRange {
        clauses: compiler.compile(&expression, false, 1)?,
    })
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ModelWire {
    data_ranges: Vec<RangeWire>,
    definitions: Vec<DefinitionWire>,
    record: String,
    schema_version: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DefinitionWire {
    data_range: RangeWire,
    datatype_iri: String,
    record: String,
    schema_version: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RangeWire {
    datatype_iri: Option<String>,
    facets: Vec<FacetWire>,
    kind: String,
    operands: Vec<Self>,
    record: String,
    schema_version: u32,
    values: Vec<Value>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct FacetWire {
    facet_iri: String,
    record: String,
    schema_version: u32,
    value: Value,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpressionKind {
    Datatype,
    Opaque,
    Restriction,
    Intersection,
    Union,
    Complement,
    Enumeration,
}

impl ExpressionKind {
    fn parse(value: &str) -> Result<Self, DatatypeError> {
        match value {
            "datatype" => Ok(Self::Datatype),
            "opaque" => Ok(Self::Opaque),
            "restriction" => Ok(Self::Restriction),
            "intersection" => Ok(Self::Intersection),
            "union" => Ok(Self::Union),
            "complement" => Ok(Self::Complement),
            "enumeration" => Ok(Self::Enumeration),
            _ => Err(DatatypeError::invalid("unknown data-range payload kind")),
        }
    }
}

#[derive(Clone, Debug)]
struct SemanticLiteral {
    identity: DataIdentity,
    comparison: ComparisonValue,
    canonical: Vec<u8>,
}

#[derive(Clone, Debug)]
struct DecodedFacet {
    facet_iri: String,
    value: SemanticLiteral,
    canonical: Vec<u8>,
}

#[derive(Clone, Debug)]
struct RangeExpression {
    kind: ExpressionKind,
    datatype_iri: Option<String>,
    operands: Vec<Self>,
    facets: Vec<DecodedFacet>,
    values: Vec<SemanticLiteral>,
    canonical: Vec<u8>,
}

impl RangeExpression {
    fn contains_opaque(&self) -> bool {
        self.kind == ExpressionKind::Opaque || self.operands.iter().any(Self::contains_opaque)
    }

    fn references(&self, output: &mut BTreeSet<String>) {
        if self.kind == ExpressionKind::Datatype {
            if let Some(iri) = &self.datatype_iri {
                if !is_supported_datatype(iri) {
                    output.insert(iri.clone());
                }
            }
        }
        for operand in &self.operands {
            operand.references(output);
        }
    }
}

struct DecodeContext<'a, C> {
    limits: RangeWireLimits,
    opaque_policy: OpaqueRangePolicy,
    control: &'a C,
    nodes: u64,
}

impl<'a, C: DatatypeControl> DecodeContext<'a, C> {
    const fn new(
        limits: RangeWireLimits,
        opaque_policy: OpaqueRangePolicy,
        control: &'a C,
    ) -> Self {
        Self {
            limits,
            opaque_policy,
            control,
            nodes: 0,
        }
    }

    fn poll(&mut self) -> Result<(), DatatypeError> {
        self.nodes = self.nodes.checked_add(1).ok_or_else(|| {
            DatatypeError::resource(
                "max_data_range_nodes",
                u64::MAX,
                self.limits.max_data_range_nodes,
            )
        })?;
        if self.nodes > self.limits.max_data_range_nodes {
            return Err(DatatypeError::resource(
                "max_data_range_nodes",
                self.nodes,
                self.limits.max_data_range_nodes,
            ));
        }
        if self.nodes == 1 || self.nodes % self.limits.cancellation_poll_stride == 0 {
            self.control.poll()?;
        }
        Ok(())
    }

    fn decode_range(
        &mut self,
        wire: &RangeWire,
        depth: u64,
    ) -> Result<RangeExpression, DatatypeError> {
        self.poll()?;
        if depth > self.limits.max_data_range_depth {
            return Err(DatatypeError::resource(
                "max_data_range_depth",
                depth,
                self.limits.max_data_range_depth,
            ));
        }
        if wire.record != "data_range_semantic" || wire.schema_version != SCHEMA_VERSION {
            return Err(DatatypeError::invalid(
                "unsupported data-range record or schema version",
            ));
        }
        let kind = ExpressionKind::parse(&wire.kind)?;
        if let Some(iri) = &wire.datatype_iri {
            validate_iri(iri)?;
        }
        let canonical = serde_json::to_vec(wire)?;
        let mut operands = Vec::new();
        for operand in &wire.operands {
            operands.push(self.decode_range(operand, depth.saturating_add(1))?);
        }
        let mut facets = Vec::new();
        for facet in &wire.facets {
            self.poll()?;
            if facet.record != "facet_semantic" || facet.schema_version != SCHEMA_VERSION {
                return Err(DatatypeError::invalid(
                    "unsupported facet semantic record or schema version",
                ));
            }
            validate_iri(&facet.facet_iri)?;
            facets.push(DecodedFacet {
                facet_iri: facet.facet_iri.clone(),
                value: decode_nested_literal(&facet.value, self.limits, self.control)?,
                canonical: serde_json::to_vec(facet)?,
            });
        }
        let mut values = Vec::new();
        for value in &wire.values {
            self.poll()?;
            values.push(decode_nested_literal(value, self.limits, self.control)?);
        }
        validate_shape(kind, wire, &operands, &facets, &values)?;
        if kind == ExpressionKind::Opaque && self.opaque_policy == OpaqueRangePolicy::Reject {
            return Err(unsupported_datatype(
                wire.datatype_iri.as_deref().unwrap_or("<missing>"),
            ));
        }
        Ok(RangeExpression {
            kind,
            datatype_iri: wire.datatype_iri.clone(),
            operands,
            facets,
            values,
            canonical,
        })
    }
}

fn validate_shape(
    kind: ExpressionKind,
    wire: &RangeWire,
    operands: &[RangeExpression],
    facets: &[DecodedFacet],
    values: &[SemanticLiteral],
) -> Result<(), DatatypeError> {
    let datatype = wire.datatype_iri.is_some();
    let valid = match kind {
        ExpressionKind::Datatype | ExpressionKind::Opaque => {
            datatype && operands.is_empty() && facets.is_empty() && values.is_empty()
        }
        ExpressionKind::Restriction => {
            datatype && operands.is_empty() && !facets.is_empty() && values.is_empty()
        }
        ExpressionKind::Intersection | ExpressionKind::Union => {
            !datatype && operands.len() >= 2 && facets.is_empty() && values.is_empty()
        }
        ExpressionKind::Complement => {
            !datatype && operands.len() == 1 && facets.is_empty() && values.is_empty()
        }
        ExpressionKind::Enumeration => {
            !datatype && operands.is_empty() && facets.is_empty() && !values.is_empty()
        }
    };
    if !valid {
        return Err(DatatypeError::invalid(
            "data-range semantic payload fields do not match its kind",
        ));
    }
    if matches!(kind, ExpressionKind::Intersection | ExpressionKind::Union) {
        if operands.iter().any(|operand| operand.kind == kind) {
            return Err(DatatypeError::invalid(
                "canonical n-ary data-range operands are not flattened",
            ));
        }
        require_strictly_sorted(
            operands.iter().map(|operand| operand.canonical.as_slice()),
            "data-range operands",
        )?;
    }
    if kind == ExpressionKind::Restriction {
        require_strictly_sorted(
            facets.iter().map(|facet| facet.canonical.as_slice()),
            "facet restrictions",
        )?;
    }
    if kind == ExpressionKind::Enumeration {
        require_strictly_sorted(
            values.iter().map(|value| value.canonical.as_slice()),
            "enumeration values",
        )?;
    }
    Ok(())
}

fn require_strictly_sorted<'a>(
    values: impl IntoIterator<Item = &'a [u8]>,
    name: &str,
) -> Result<(), DatatypeError> {
    let mut previous: Option<&[u8]> = None;
    for value in values {
        if previous.is_some_and(|known| known >= value) {
            return Err(DatatypeError::invalid(format!(
                "canonical {name} are not strictly sorted and unique"
            )));
        }
        previous = Some(value);
    }
    Ok(())
}

fn decode_nested_literal(
    value: &Value,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<SemanticLiteral, DatatypeError> {
    let canonical = serde_json::to_vec(value)?;
    let decoded = decode_literal_semantic(0, &canonical, limits.values, control)?;
    let DecodedLiteral::Semantic(literal) = decoded else {
        return Err(DatatypeError::invalid(
            "data-range facets and enumerations cannot contain opaque literals",
        ));
    };
    Ok(SemanticLiteral {
        identity: literal.data_identity,
        comparison: literal.comparison,
        canonical,
    })
}

fn validate_definition_graph(
    roots: &[RangeExpression],
    definitions: &BTreeMap<String, RangeExpression>,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<(), DatatypeError> {
    let names: BTreeSet<_> = definitions.keys().cloned().collect();
    let mut graph = BTreeMap::new();
    for (index, (name, expression)) in definitions.iter().enumerate() {
        poll_index(index, limits, control)?;
        let mut references = BTreeSet::new();
        expression.references(&mut references);
        for reference in &references {
            if !names.contains(reference) {
                return Err(unsupported_datatype(reference));
            }
        }
        graph.insert(name.clone(), references);
    }
    for (index, root) in roots.iter().enumerate() {
        poll_index(index, limits, control)?;
        let mut references = BTreeSet::new();
        root.references(&mut references);
        for reference in references {
            if !names.contains(&reference) {
                return Err(unsupported_datatype(&reference));
            }
        }
    }
    let mut indegrees: BTreeMap<String, usize> =
        graph.keys().map(|name| (name.clone(), 0)).collect();
    for references in graph.values() {
        for reference in references {
            let value = indegrees
                .get_mut(reference)
                .ok_or_else(|| DatatypeError::invalid("datatype graph reference is absent"))?;
            *value = value.saturating_add(1);
        }
    }
    let mut ready: BTreeSet<String> = indegrees
        .iter()
        .filter(|(_, value)| **value == 0)
        .map(|(name, _)| name.clone())
        .collect();
    let mut visited = 0_usize;
    while let Some(name) = ready.pop_first() {
        visited += 1;
        poll_index(visited, limits, control)?;
        if let Some(references) = graph.get(&name) {
            for reference in references {
                let degree = indegrees
                    .get_mut(reference)
                    .ok_or_else(|| DatatypeError::invalid("datatype graph node is absent"))?;
                *degree = degree.saturating_sub(1);
                if *degree == 0 {
                    ready.insert(reference.clone());
                }
            }
        }
    }
    if visited != definitions.len() {
        return Err(DatatypeError::invalid(
            "custom datatype definitions must form an acyclic graph",
        ));
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct Atom {
    canonical: Vec<u8>,
    payload: AtomPayload,
}

impl Atom {
    fn contains(
        &self,
        value: &DataIdentity,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        match &self.payload {
            AtomPayload::Universal => Ok(true),
            AtomPayload::Family(range) => range.contains(value, limits, control),
            AtomPayload::Enumeration(values) => Ok(values.contains(value)),
        }
    }
}

#[derive(Clone, Debug)]
enum AtomPayload {
    Universal,
    Family(FamilyRange),
    Enumeration(BTreeSet<DataIdentity>),
}

#[derive(Clone, Debug)]
struct SignedAtom {
    atom: Atom,
    positive: bool,
}

type Clause = Vec<SignedAtom>;
type Dnf = Vec<Clause>;

struct DnfCompiler<'a, C> {
    definitions: &'a BTreeMap<String, RangeExpression>,
    limits: RangeWireLimits,
    control: &'a C,
    nodes: u64,
    atom_cache: HashMap<Vec<u8>, Atom>,
}

impl<'a, C: DatatypeControl> DnfCompiler<'a, C> {
    fn new(
        definitions: &'a BTreeMap<String, RangeExpression>,
        limits: RangeWireLimits,
        control: &'a C,
    ) -> Self {
        Self {
            definitions,
            limits,
            control,
            nodes: 0,
            atom_cache: HashMap::new(),
        }
    }

    fn compile(
        &mut self,
        expression: &RangeExpression,
        negated: bool,
        depth: u64,
    ) -> Result<Dnf, DatatypeError> {
        self.visit(depth)?;
        match expression.kind {
            ExpressionKind::Opaque => Err(unsupported_datatype(
                expression.datatype_iri.as_deref().unwrap_or("<missing>"),
            )),
            ExpressionKind::Datatype => {
                let iri = expression
                    .datatype_iri
                    .as_ref()
                    .ok_or_else(|| DatatypeError::invalid("datatype atom has no IRI"))?;
                if let Some(definition) = self.definitions.get(iri) {
                    return self.compile(definition, negated, depth.saturating_add(1));
                }
                self.atom_dnf(expression, !negated)
            }
            ExpressionKind::Restriction | ExpressionKind::Enumeration => {
                self.atom_dnf(expression, !negated)
            }
            ExpressionKind::Complement => {
                self.compile(&expression.operands[0], !negated, depth.saturating_add(1))
            }
            ExpressionKind::Intersection | ExpressionKind::Union => {
                let intersection = expression.kind == ExpressionKind::Intersection;
                let combine_with_and = intersection != negated;
                let mut result = if combine_with_and {
                    vec![Vec::new()]
                } else {
                    Vec::new()
                };
                for operand in &expression.operands {
                    let compiled = self.compile(operand, negated, depth.saturating_add(1))?;
                    result = if combine_with_and {
                        and_dnf(&result, &compiled, self.limits, self.control)?
                    } else {
                        let mut combined = result;
                        combined.extend(compiled);
                        normalize_dnf(combined, self.limits, self.control)?
                    };
                }
                Ok(result)
            }
        }
    }

    fn atom_dnf(
        &mut self,
        expression: &RangeExpression,
        positive: bool,
    ) -> Result<Dnf, DatatypeError> {
        let atom = if let Some(value) = self.atom_cache.get(&expression.canonical) {
            value.clone()
        } else {
            let value = compile_atom(expression, self.limits, self.control)?;
            self.atom_cache
                .insert(expression.canonical.clone(), value.clone());
            value
        };
        let clause = merge_clause(&[], &[SignedAtom { atom, positive }]);
        match clause {
            None => Ok(Vec::new()),
            Some(value) => normalize_dnf(vec![value], self.limits, self.control),
        }
    }

    fn visit(&mut self, depth: u64) -> Result<(), DatatypeError> {
        self.nodes = self.nodes.saturating_add(1);
        if depth > self.limits.max_data_range_depth {
            return Err(DatatypeError::resource(
                "max_data_range_depth",
                depth,
                self.limits.max_data_range_depth,
            ));
        }
        if self.nodes > self.limits.max_data_range_nodes {
            return Err(DatatypeError::resource(
                "max_data_range_nodes",
                self.nodes,
                self.limits.max_data_range_nodes,
            ));
        }
        if self.nodes == 1 || self.nodes % self.limits.cancellation_poll_stride == 0 {
            self.control.poll()?;
        }
        Ok(())
    }
}

fn and_dnf(
    left: &Dnf,
    right: &Dnf,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Dnf, DatatypeError> {
    if left.is_empty() || right.is_empty() {
        return Ok(Vec::new());
    }
    let mut clauses = Vec::new();
    for first in left {
        for second in right {
            if let Some(merged) = merge_clause(first, second) {
                clauses.push(merged);
                check_dnf_size(clauses.len(), limits)?;
            }
            if clauses.len() % usize::try_from(limits.cancellation_poll_stride).unwrap_or(1) == 0 {
                control.poll()?;
            }
        }
    }
    normalize_dnf(clauses, limits, control)
}

fn not_dnf(
    value: &Dnf,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Dnf, DatatypeError> {
    if value.is_empty() {
        return Ok(vec![Vec::new()]);
    }
    let mut result = vec![Vec::new()];
    for (index, clause) in value.iter().enumerate() {
        poll_index(index, limits, control)?;
        if clause.is_empty() {
            return Ok(Vec::new());
        }
        let alternatives: Dnf = clause
            .iter()
            .map(|atom| {
                vec![SignedAtom {
                    atom: atom.atom.clone(),
                    positive: !atom.positive,
                }]
            })
            .collect();
        result = and_dnf(&result, &alternatives, limits, control)?;
    }
    Ok(result)
}

fn merge_clause(left: &[SignedAtom], right: &[SignedAtom]) -> Option<Clause> {
    let mut selected: BTreeMap<Vec<u8>, SignedAtom> = BTreeMap::new();
    for atom in left.iter().chain(right) {
        if matches!(atom.atom.payload, AtomPayload::Universal) {
            if !atom.positive {
                return None;
            }
            continue;
        }
        if let Some(previous) = selected.get(&atom.atom.canonical) {
            if previous.positive != atom.positive {
                return None;
            }
        }
        selected.insert(atom.atom.canonical.clone(), atom.clone());
    }
    Some(selected.into_values().collect())
}

fn normalize_dnf(
    mut clauses: Dnf,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Dnf, DatatypeError> {
    clauses.sort_by(compare_clause);
    clauses.dedup_by(|left, right| compare_clause(left, right) == Ordering::Equal);
    if clauses.iter().any(Vec::is_empty) {
        return Ok(vec![Vec::new()]);
    }
    let mut retained: Dnf = Vec::new();
    for clause in clauses {
        if retained.iter().any(|known| clause_subset(known, &clause)) {
            continue;
        }
        retained.retain(|known| !clause_subset(&clause, known));
        retained.push(clause);
        check_dnf_size(retained.len(), limits)?;
        if retained.len() % usize::try_from(limits.cancellation_poll_stride).unwrap_or(1) == 0 {
            control.poll()?;
        }
    }
    retained.sort_by(compare_clause);
    Ok(retained)
}

fn compare_clause(left: &Clause, right: &Clause) -> Ordering {
    left.iter()
        .map(signed_atom_key)
        .cmp(right.iter().map(signed_atom_key))
}

fn dnf_digest(value: &Dnf) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"pyhermit/data-domain-witness/v1\0");
    for clause in value {
        digest.update(b"[");
        for atom in clause {
            digest.update(if atom.positive { b"+" } else { b"-" });
            digest.update(
                u64::try_from(atom.atom.canonical.len())
                    .unwrap_or(u64::MAX)
                    .to_be_bytes(),
            );
            digest.update(&atom.atom.canonical);
        }
        digest.update(b"]");
    }
    digest.finalize().into()
}

fn signed_atom_key(value: &SignedAtom) -> (&[u8], bool) {
    (&value.atom.canonical, !value.positive)
}

fn clause_subset(left: &Clause, right: &Clause) -> bool {
    left.iter().all(|candidate| {
        right.iter().any(|value| {
            candidate.positive == value.positive && candidate.atom.canonical == value.atom.canonical
        })
    })
}

fn check_dnf_size(observed: usize, limits: RangeWireLimits) -> Result<(), DatatypeError> {
    let observed = u64::try_from(observed).unwrap_or(u64::MAX);
    if observed > limits.max_dnf_clauses {
        return Err(DatatypeError::resource(
            "max_dnf_clauses",
            observed,
            limits.max_dnf_clauses,
        ));
    }
    Ok(())
}

fn preflight_bytes(
    bytes: &[u8],
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<(), DatatypeError> {
    control.poll()?;
    let length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    if length > limits.max_payload_bytes {
        return Err(DatatypeError::resource(
            "max_payload_bytes",
            length,
            limits.max_payload_bytes,
        ));
    }
    control.observe_memory(length)?;
    scan_json_nesting(bytes, limits.max_json_nesting)?;
    Ok(())
}

fn scan_json_nesting(bytes: &[u8], maximum: u64) -> Result<(), DatatypeError> {
    let mut depth = 0_u64;
    let mut in_string = false;
    let mut escaped = false;
    for byte in bytes {
        if in_string {
            if escaped {
                escaped = false;
            } else if *byte == b'\\' {
                escaped = true;
            } else if *byte == b'"' {
                in_string = false;
            }
            continue;
        }
        if *byte == b'"' {
            in_string = true;
        } else if matches!(*byte, b'{' | b'[') {
            depth = depth.saturating_add(1);
            if depth > maximum {
                return Err(DatatypeError::resource("max_json_nesting", depth, maximum));
            }
        } else if matches!(*byte, b'}' | b']') {
            depth = depth.saturating_sub(1);
        }
    }
    Ok(())
}

fn require_canonical<T: Serialize>(bytes: &[u8], value: &T) -> Result<(), DatatypeError> {
    if serde_json::to_vec(value)? == bytes {
        Ok(())
    } else {
        Err(DatatypeError::invalid(
            "datatype semantic payload is not canonical JSON",
        ))
    }
}

fn validate_iri(value: &str) -> Result<(), DatatypeError> {
    if value.is_empty()
        || !value.contains(':')
        || value
            .chars()
            .any(|character| character.is_control() || character.is_whitespace())
    {
        return Err(DatatypeError::invalid("datatype or facet IRI is invalid"));
    }
    Ok(())
}

fn poll_index(
    index: usize,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<(), DatatypeError> {
    let stride = usize::try_from(limits.cancellation_poll_stride).unwrap_or(1);
    if index == 0 || index % stride == 0 {
        control.poll()?;
    }
    Ok(())
}

fn unsupported_datatype(iri: &str) -> DatatypeError {
    DatatypeError::invalid(format!(
        "opaque or unsupported datatype semantics cannot be evaluated: {iri}"
    ))
}

fn cardinality_from_count(value: BigUint) -> Cardinality {
    if value.is_zero() {
        Cardinality::Empty
    } else {
        Cardinality::Finite(value)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NativeDataValueFamily {
    Numeric,
    Boolean,
    Float,
    Double,
    String,
    HexBinary,
    Base64Binary,
    Uri,
    Xml,
    DateTime,
}

type Family = NativeDataValueFamily;

const FAMILIES: [Family; 10] = [
    Family::Numeric,
    Family::Boolean,
    Family::Float,
    Family::Double,
    Family::String,
    Family::HexBinary,
    Family::Base64Binary,
    Family::Uri,
    Family::Xml,
    Family::DateTime,
];

#[derive(Clone, Debug)]
enum FamilyRange {
    Numeric(NumericRange),
    Boolean(BooleanRange),
    Ieee(IEEERange),
    String(StringFamilyRange),
    Binary(BinaryRange),
    Uri(RegexRange),
    Xml(bool),
    DateTime(DateTimeRange),
}

impl FamilyRange {
    const fn family(&self) -> Family {
        match self {
            Self::Numeric(_) => Family::Numeric,
            Self::Boolean(_) => Family::Boolean,
            Self::Ieee(value) => match value.format() {
                IEEEFormat::Float32 => Family::Float,
                IEEEFormat::Float64 => Family::Double,
            },
            Self::String(_) => Family::String,
            Self::Binary(value) => match value.kind() {
                BinaryKind::Hex => Family::HexBinary,
                BinaryKind::Base64 => Family::Base64Binary,
            },
            Self::Uri(_) => Family::Uri,
            Self::Xml(_) => Family::Xml,
            Self::DateTime(_) => Family::DateTime,
        }
    }

    fn contains(
        &self,
        identity: &DataIdentity,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        match (self, identity) {
            (Self::Numeric(range), DataIdentity::Numeric(value)) => range.contains(value),
            (Self::Boolean(range), DataIdentity::Boolean(value)) => Ok(range.contains(*value)),
            (Self::Ieee(range), value) => Ok(range.contains(value)),
            (Self::String(range), DataIdentity::String { text, language }) => {
                range.contains(text, language.as_deref(), limits, control)
            }
            (Self::Binary(range), value) => Ok(range.contains(value)),
            (Self::Uri(range), DataIdentity::Uri(value)) => {
                range.language.fullmatch(value, limits.regex, control)
            }
            (Self::Xml(include_all), DataIdentity::Xml(_)) => Ok(*include_all),
            (
                Self::DateTime(range),
                DataIdentity::DateTime {
                    local,
                    timezone_offset_minutes,
                    ..
                },
            ) => range.contains(local, *timezone_offset_minutes),
            _ => Ok(false),
        }
    }

    fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        match (self, other) {
            (Self::Numeric(left), Self::Numeric(right)) => {
                Ok(Self::Numeric(left.intersection(right)?))
            }
            (Self::Boolean(left), Self::Boolean(right)) => {
                Ok(Self::Boolean(left.intersection(*right)))
            }
            (Self::Ieee(left), Self::Ieee(right)) => Ok(Self::Ieee(left.intersection(right)?)),
            (Self::String(left), Self::String(right)) => Ok(Self::String(left.intersection(right))),
            (Self::Binary(left), Self::Binary(right)) => {
                Ok(Self::Binary(left.intersection(right)?))
            }
            (Self::Uri(left), Self::Uri(right)) => Ok(Self::Uri(left.intersection(right))),
            (Self::Xml(left), Self::Xml(right)) => Ok(Self::Xml(*left && *right)),
            (Self::DateTime(left), Self::DateTime(right)) => {
                Ok(Self::DateTime(left.intersection(right)?))
            }
            _ => Err(DatatypeError::invalid(
                "family-range intersection requires one value family",
            )),
        }
    }

    fn complement(&self) -> Result<Self, DatatypeError> {
        match self {
            Self::Numeric(value) => Ok(Self::Numeric(value.complement()?)),
            Self::Boolean(value) => Ok(Self::Boolean(value.complement())),
            Self::Ieee(value) => Ok(Self::Ieee(value.complement()?)),
            Self::String(value) => Ok(Self::String(value.complement())),
            Self::Binary(value) => Ok(Self::Binary(value.complement())),
            Self::Uri(value) => Ok(Self::Uri(value.complement())),
            Self::Xml(value) => Ok(Self::Xml(!value)),
            Self::DateTime(value) => Ok(Self::DateTime(value.complement()?)),
        }
    }

    fn is_empty(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        match self {
            Self::Numeric(value) => Ok(value.is_empty_exact()),
            Self::Boolean(value) => Ok(value.is_empty_exact()),
            Self::Ieee(value) => Ok(value.is_empty_exact()),
            Self::String(value) => value.is_empty(limits, control),
            Self::Binary(value) => Ok(value.is_empty_exact()),
            Self::Uri(value) => value.language.is_empty_exact(limits.regex, control),
            Self::Xml(value) => Ok(!value),
            Self::DateTime(value) => Ok(value.is_empty()),
        }
    }

    fn cardinality(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Cardinality, DatatypeError> {
        match self {
            Self::Numeric(value) => value.cardinality(),
            Self::Boolean(value) => Ok(value.cardinality()),
            Self::Ieee(value) => Ok(value.cardinality()),
            Self::String(value) => value.cardinality(limits, control),
            Self::Binary(value) => value.cardinality(limits.ranges, control),
            Self::Uri(value) => regex_cardinality(&value.language, limits, control),
            Self::Xml(value) => Ok(if *value {
                Cardinality::Infinite
            } else {
                Cardinality::Empty
            }),
            Self::DateTime(value) => value.cardinality(),
        }
    }

    fn cardinality_up_to(
        &self,
        maximum: u64,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<u64, DatatypeError> {
        if maximum == 0 {
            return Ok(0);
        }
        match self {
            Self::Numeric(value) => Ok(capped_cardinality(&value.cardinality()?, maximum)),
            Self::Boolean(value) => Ok(capped_cardinality(&value.cardinality(), maximum)),
            Self::Ieee(value) => Ok(capped_cardinality(&value.cardinality(), maximum)),
            Self::String(value) => value.cardinality_up_to(maximum, limits, control),
            Self::Binary(value) => value.cardinality_up_to(maximum, control),
            Self::Uri(value) => value
                .language
                .cardinality_up_to(maximum, limits.regex, control),
            Self::Xml(value) => Ok(if *value { maximum } else { 0 }),
            Self::DateTime(value) => Ok(capped_cardinality(&value.cardinality()?, maximum)),
        }
    }

    fn enumerate(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        match self {
            Self::Numeric(value) => Ok(value
                .enumerate_values(limits.ranges, control)?
                .into_iter()
                .map(DataIdentity::Numeric)
                .collect()),
            Self::Boolean(value) => Ok(value
                .enumerate_values()
                .into_iter()
                .map(DataIdentity::Boolean)
                .collect()),
            Self::Ieee(value) => value.enumerate_values(limits.ranges, control),
            Self::String(value) => value.enumerate(limits, control),
            Self::Binary(value) => value.enumerate_values(limits.ranges, control),
            Self::Uri(value) => Ok(value
                .language
                .enumerate_strings(limits.regex, control)?
                .into_iter()
                .map(DataIdentity::Uri)
                .collect()),
            Self::Xml(false) => Ok(Vec::new()),
            Self::Xml(true) => Err(DatatypeError::invalid(
                "cannot enumerate the infinite XML literal space",
            )),
            Self::DateTime(value) => value.enumerate(limits, control),
        }
    }

    fn first_identity(
        &self,
        excluding: &BTreeSet<DataIdentity>,
        numeric_exclusions: &[NumericRange],
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        match self {
            Self::Numeric(value) => {
                let mut blocked: Vec<_> = excluding
                    .iter()
                    .filter_map(|identity| match identity {
                        DataIdentity::Numeric(value) => Some(value.clone()),
                        _ => None,
                    })
                    .collect();
                let attempts = u64::try_from(blocked.len())
                    .unwrap_or(u64::MAX)
                    .saturating_add(
                        u64::try_from(numeric_exclusions.len())
                            .unwrap_or(u64::MAX)
                            .saturating_mul(18),
                    )
                    .saturating_add(32)
                    .min(limits.ranges.max_witness_steps);
                for step in 0..attempts {
                    poll_index(usize::try_from(step).unwrap_or(usize::MAX), limits, control)?;
                    let Some(candidate) = value.first_value(&blocked, limits.ranges, control)?
                    else {
                        return Ok(None);
                    };
                    let mut retained = true;
                    for excluded in numeric_exclusions {
                        if excluded.contains(&candidate)? {
                            retained = false;
                            break;
                        }
                    }
                    if retained {
                        return Ok(Some(DataIdentity::Numeric(candidate)));
                    }
                    blocked.push(candidate);
                }
                Ok(None)
            }
            Self::Boolean(value) => Ok(value
                .first_value(
                    &excluding
                        .iter()
                        .filter_map(|identity| match identity {
                            DataIdentity::Boolean(value) => Some(*value),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                )
                .map(DataIdentity::Boolean)),
            Self::Ieee(value) => value.first_identity(
                &excluding.iter().cloned().collect::<Vec<_>>(),
                limits.ranges,
                control,
            ),
            Self::String(value) => value.first_identity(excluding, limits, control),
            Self::Binary(value) => value.first_identity(
                &excluding.iter().cloned().collect::<Vec<_>>(),
                limits.ranges,
                control,
            ),
            Self::Uri(value) => {
                if value.language.is_empty_exact(limits.regex, control)? {
                    return Ok(None);
                }
                let blocked = excluding
                    .iter()
                    .filter_map(|identity| match identity {
                        DataIdentity::Uri(value) => Some(value.clone()),
                        _ => None,
                    })
                    .collect();
                Ok(Some(DataIdentity::Uri(value.language.first_string(
                    &blocked,
                    limits.regex,
                    control,
                )?)))
            }
            Self::Xml(false) => Ok(None),
            Self::Xml(true) => {
                let blocked: BTreeSet<_> = excluding
                    .iter()
                    .filter_map(|identity| match identity {
                        DataIdentity::Xml(value) => Some(value.as_str()),
                        _ => None,
                    })
                    .collect();
                for index in 0..=blocked.len() {
                    let value = if index == 0 {
                        String::new()
                    } else {
                        (index - 1).to_string()
                    };
                    if !blocked.contains(value.as_str()) {
                        return Ok(Some(DataIdentity::Xml(value)));
                    }
                }
                Ok(None)
            }
            Self::DateTime(value) => value.first_identity(excluding, limits, control),
        }
    }
}

#[derive(Clone, Debug)]
struct RegexRange {
    universe: XsdRegex,
    language: XsdRegex,
}

impl RegexRange {
    fn all() -> Self {
        let universe = XsdRegex::all();
        Self {
            universe: universe.clone(),
            language: universe,
        }
    }

    fn intersection(&self, other: &Self) -> Self {
        Self {
            universe: self.universe.clone(),
            language: self.language.intersection(&other.language),
        }
    }

    fn complement(&self) -> Self {
        Self {
            universe: self.universe.clone(),
            language: self.universe.intersection(&self.language.complement()),
        }
    }
}

fn regex_cardinality(
    value: &XsdRegex,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Cardinality, DatatypeError> {
    Ok(match value.finite_cardinality(limits.regex, control)? {
        None => Cardinality::Infinite,
        Some(value) => cardinality_from_count(value),
    })
}

fn capped_cardinality(value: &Cardinality, maximum: u64) -> u64 {
    match value {
        Cardinality::Empty => 0,
        Cardinality::Finite(value) => value.to_u64().unwrap_or(u64::MAX).min(maximum),
        Cardinality::Infinite => maximum,
    }
}

#[derive(Clone, Debug)]
struct DateTimeRange {
    zoned: NumericRange,
    unzoned: NumericRange,
    include_unzoned: bool,
}

impl DateTimeRange {
    fn all(require_timezone: bool) -> Self {
        Self {
            zoned: NumericRange::all(NumericDomain::Real),
            unzoned: if require_timezone {
                NumericRange::empty(NumericDomain::Real)
            } else {
                NumericRange::all(NumericDomain::Real)
            },
            // Family atoms are always represented relative to the complete
            // dateTime family. dateTimeStamp selects an empty unzoned component;
            // retaining the larger universe makes its negation select every
            // unzoned dateTime value, matching the mixed-domain algebra.
            include_unzoned: true,
        }
    }

    fn contains(
        &self,
        local: &ExactRational,
        timezone: Option<i16>,
    ) -> Result<bool, DatatypeError> {
        match timezone {
            Some(offset) => self
                .zoned
                .contains(&local.subtract_integer(i64::from(offset) * 60)),
            None if self.include_unzoned => self.unzoned.contains(local),
            None => Ok(false),
        }
    }

    fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        let include_unzoned = self.include_unzoned && other.include_unzoned;
        Ok(Self {
            zoned: self.zoned.intersection(&other.zoned)?,
            unzoned: if include_unzoned {
                self.unzoned.intersection(&other.unzoned)?
            } else {
                NumericRange::empty(NumericDomain::Real)
            },
            include_unzoned,
        })
    }

    fn complement(&self) -> Result<Self, DatatypeError> {
        Ok(Self {
            zoned: self.zoned.complement()?,
            unzoned: if self.include_unzoned {
                self.unzoned.complement()?
            } else {
                NumericRange::empty(NumericDomain::Real)
            },
            include_unzoned: self.include_unzoned,
        })
    }

    fn is_empty(&self) -> bool {
        self.zoned.is_empty_exact() && self.unzoned.is_empty_exact()
    }

    fn cardinality(&self) -> Result<Cardinality, DatatypeError> {
        let zoned = self.zoned.cardinality()?;
        let unzoned = self.unzoned.cardinality()?;
        match (zoned, unzoned) {
            (Cardinality::Infinite, _) | (_, Cardinality::Infinite) => Ok(Cardinality::Infinite),
            (left, right) => {
                let left = finite_count(left) * BigUint::from(1_681_u16);
                Ok(cardinality_from_count(left + finite_count(right)))
            }
        }
    }

    fn enumerate(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        let cardinality = self.cardinality()?;
        let count = materializable_count(&cardinality, limits.ranges.max_enumeration_values)?;
        control.observe_memory(count.saturating_mul(32))?;
        let mut output = Vec::with_capacity(usize::try_from(count).map_err(|_| {
            DatatypeError::resource(
                "max_enumeration_values",
                count,
                limits.ranges.max_enumeration_values,
            )
        })?);
        let mut work = 0_usize;
        for point in self.zoned.enumerate_values(limits.ranges, control)? {
            for offset in -840_i16..=840_i16 {
                output.push(DataIdentity::DateTime {
                    local: point.subtract_integer(-(i64::from(offset) * 60)),
                    timezone_offset_minutes: Some(offset),
                    hermit_end_of_day: false,
                });
                work += 1;
                poll_index(work, limits, control)?;
            }
        }
        for point in self.unzoned.enumerate_values(limits.ranges, control)? {
            output.push(DataIdentity::DateTime {
                local: point,
                timezone_offset_minutes: None,
                hermit_end_of_day: false,
            });
        }
        Ok(output)
    }

    fn first_identity(
        &self,
        excluding: &BTreeSet<DataIdentity>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        let zoned_timelines: Vec<_> = excluding
            .iter()
            .filter_map(|identity| match identity {
                DataIdentity::DateTime {
                    local,
                    timezone_offset_minutes: Some(offset),
                    ..
                } => Some(local.subtract_integer(i64::from(*offset) * 60)),
                _ => None,
            })
            .collect();
        if let Some(point) = self
            .zoned
            .first_value(&zoned_timelines, limits.ranges, control)?
        {
            for (index, offset) in (-840_i16..=840_i16).enumerate() {
                poll_index(index, limits, control)?;
                let candidate = DataIdentity::DateTime {
                    local: point.subtract_integer(-(i64::from(offset) * 60)),
                    timezone_offset_minutes: Some(offset),
                    hermit_end_of_day: false,
                };
                if !excluding.contains(&candidate) && self.contains_identity(&candidate)? {
                    return Ok(Some(candidate));
                }
            }
        }
        let unzoned: Vec<_> = excluding
            .iter()
            .filter_map(|identity| match identity {
                DataIdentity::DateTime {
                    local,
                    timezone_offset_minutes: None,
                    ..
                } => Some(local.clone()),
                _ => None,
            })
            .collect();
        if let Some(point) = self.unzoned.first_value(&unzoned, limits.ranges, control)? {
            let candidate = DataIdentity::DateTime {
                local: point,
                timezone_offset_minutes: None,
                hermit_end_of_day: false,
            };
            if !excluding.contains(&candidate) && self.contains_identity(&candidate)? {
                return Ok(Some(candidate));
            }
        }
        Ok(None)
    }

    fn contains_identity(&self, value: &DataIdentity) -> Result<bool, DatatypeError> {
        let DataIdentity::DateTime {
            local,
            timezone_offset_minutes,
            ..
        } = value
        else {
            return Ok(false);
        };
        self.contains(local, *timezone_offset_minutes)
    }
}

fn finite_count(value: Cardinality) -> BigUint {
    match value {
        Cardinality::Empty => BigUint::zero(),
        Cardinality::Finite(value) => value,
        Cardinality::Infinite => unreachable!("caller established finite cardinality"),
    }
}

fn materializable_count(value: &Cardinality, maximum: u64) -> Result<u64, DatatypeError> {
    match value {
        Cardinality::Empty => Ok(0),
        Cardinality::Finite(value) => {
            let observed = value.to_u64().unwrap_or(u64::MAX);
            if observed > maximum {
                Err(DatatypeError::resource(
                    "max_enumeration_values",
                    observed,
                    maximum,
                ))
            } else {
                Ok(observed)
            }
        }
        Cardinality::Infinite => Err(DatatypeError::invalid(
            "cannot enumerate an infinite data range",
        )),
    }
}

#[derive(Clone, Debug)]
struct TextLanguageRectangle {
    text: XsdRegex,
    language: LanguageTagRange,
}

impl TextLanguageRectangle {
    fn intersection(&self, other: &Self) -> Self {
        Self {
            text: self.text.intersection(&other.text),
            language: self.language.intersection(&other.language),
        }
    }

    fn is_empty(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        Ok(self.text.is_empty_exact(limits.regex, control)? || self.language.is_empty())
    }
}

#[derive(Clone, Debug)]
struct StringFamilyRange {
    without_language: XsdRegex,
    with_language: Vec<TextLanguageRectangle>,
}

impl StringFamilyRange {
    fn all() -> Self {
        Self {
            without_language: XsdRegex::all(),
            with_language: vec![TextLanguageRectangle {
                text: XsdRegex::all(),
                language: LanguageTagRange::all(),
            }],
        }
    }

    fn for_datatype(
        iri: &str,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Self, DatatypeError> {
        let pattern = match iri {
            RDF_PLAIN_LITERAL | XSD_STRING => ".*",
            XSD_NORMALIZED_STRING => "[^\\t\\n\\r]*",
            XSD_TOKEN => "([^\\t\\n\\r ]+( [^\\t\\n\\r ]+)*)?",
            XSD_LANGUAGE => "[A-Za-z]{1,8}(-[A-Za-z0-9]{1,8})*",
            XSD_NAME => "\\i\\c*",
            XSD_NCNAME => "[\\i-[:]][\\c-[:]]*",
            XSD_NMTOKEN => "\\c+",
            _ => return Err(unsupported_datatype(iri)),
        };
        let text = XsdRegex::compile(pattern, limits.regex, control)?;
        Ok(Self {
            without_language: text.clone(),
            with_language: if iri == RDF_PLAIN_LITERAL {
                vec![TextLanguageRectangle {
                    text,
                    language: LanguageTagRange::all(),
                }]
            } else {
                Vec::new()
            },
        })
    }

    fn contains(
        &self,
        text: &str,
        language: Option<&str>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        match language {
            None => self.without_language.fullmatch(text, limits.regex, control),
            Some(language) => {
                for clause in &self.with_language {
                    if clause.language.contains(language)
                        && clause.text.fullmatch(text, limits.regex, control)?
                    {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    fn intersection(&self, other: &Self) -> Self {
        Self {
            without_language: self.without_language.intersection(&other.without_language),
            with_language: self
                .with_language
                .iter()
                .flat_map(|left| {
                    other
                        .with_language
                        .iter()
                        .map(move |right| left.intersection(right))
                })
                .collect(),
        }
    }

    fn complement(&self) -> Self {
        let mut tagged = vec![TextLanguageRectangle {
            text: XsdRegex::all(),
            language: LanguageTagRange::all(),
        }];
        for excluded in &self.with_language {
            let mut expanded = Vec::new();
            for retained in tagged {
                expanded.push(TextLanguageRectangle {
                    text: retained.text.intersection(&excluded.text.complement()),
                    language: retained.language.clone(),
                });
                expanded.push(TextLanguageRectangle {
                    text: retained.text,
                    language: retained
                        .language
                        .intersection(&excluded.language.complement()),
                });
            }
            tagged = expanded;
        }
        Self {
            without_language: self.without_language.complement(),
            with_language: tagged,
        }
    }

    fn with_text_pattern(&self, pattern: &XsdRegex) -> Self {
        Self {
            without_language: self.without_language.intersection(pattern),
            with_language: self
                .with_language
                .iter()
                .map(|clause| TextLanguageRectangle {
                    text: clause.text.intersection(pattern),
                    language: clause.language.clone(),
                })
                .collect(),
        }
    }

    fn with_language(&self, language: &LanguageTagRange) -> Self {
        Self {
            without_language: XsdRegex::empty(),
            with_language: self
                .with_language
                .iter()
                .map(|clause| TextLanguageRectangle {
                    text: clause.text.clone(),
                    language: clause.language.intersection(language),
                })
                .collect(),
        }
    }

    fn is_empty(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        if !self
            .without_language
            .is_empty_exact(limits.regex, control)?
        {
            return Ok(false);
        }
        for clause in &self.with_language {
            if !clause.is_empty(limits, control)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn disjoint_rectangles(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<TextLanguageRectangle>, DatatypeError> {
        let mut output: Vec<TextLanguageRectangle> = Vec::new();
        for clause in &self.with_language {
            let mut pending = vec![clause.clone()];
            for excluded in &output {
                let mut retained = Vec::new();
                for value in pending {
                    let pieces = [
                        TextLanguageRectangle {
                            text: value.text.intersection(&excluded.text.complement()),
                            language: value.language.clone(),
                        },
                        TextLanguageRectangle {
                            text: value.text.intersection(&excluded.text),
                            language: value.language.intersection(&excluded.language.complement()),
                        },
                    ];
                    for piece in pieces {
                        if !piece.is_empty(limits, control)? {
                            retained.push(piece);
                        }
                    }
                }
                pending = retained;
                if pending.is_empty() {
                    break;
                }
            }
            output.extend(pending);
            check_pattern_state_count(output.len(), limits)?;
            control.poll()?;
        }
        Ok(output)
    }

    fn cardinality(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Cardinality, DatatypeError> {
        let Some(mut total) = self
            .without_language
            .finite_cardinality(limits.regex, control)?
        else {
            return Ok(Cardinality::Infinite);
        };
        for clause in self.disjoint_rectangles(limits, control)? {
            let Some(text_count) = clause.text.finite_cardinality(limits.regex, control)? else {
                if !clause.language.is_empty() {
                    return Ok(Cardinality::Infinite);
                }
                continue;
            };
            let Some(language_count) = clause.language.finite_cardinality() else {
                if !text_count.is_zero() {
                    return Ok(Cardinality::Infinite);
                }
                continue;
            };
            total += text_count * language_count;
        }
        Ok(cardinality_from_count(total))
    }

    fn cardinality_up_to(
        &self,
        maximum: u64,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<u64, DatatypeError> {
        if maximum == 0 {
            return Ok(0);
        }
        let mut total = self
            .without_language
            .cardinality_up_to(maximum, limits.regex, control)?;
        if total == maximum {
            return Ok(maximum);
        }
        for clause in self.disjoint_rectangles(limits, control)? {
            let remaining = maximum - total;
            let text_count = clause
                .text
                .cardinality_up_to(remaining, limits.regex, control)?;
            if text_count == 0 {
                continue;
            }
            if text_count == remaining {
                if clause.language.cardinality_up_to(1) != 0 {
                    return Ok(maximum);
                }
                continue;
            }
            let language_limit = remaining.div_ceil(text_count);
            let language_count = clause.language.cardinality_up_to(language_limit);
            total = total.saturating_add(text_count.saturating_mul(language_count).min(remaining));
            if total == maximum {
                return Ok(maximum);
            }
        }
        Ok(total)
    }

    fn enumerate(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        let count = materializable_count(
            &self.cardinality(limits, control)?,
            limits.ranges.max_enumeration_values,
        )?;
        let mut output = BTreeSet::new();
        for text in self
            .without_language
            .enumerate_strings(limits.regex, control)?
        {
            output.insert(DataIdentity::String {
                text,
                language: None,
            });
        }
        for clause in self.disjoint_rectangles(limits, control)? {
            let texts = clause.text.enumerate_strings(limits.regex, control)?;
            let languages = clause.language.enumerate();
            for text in texts {
                for language in &languages {
                    output.insert(DataIdentity::String {
                        text: text.clone(),
                        language: Some(language.clone()),
                    });
                }
            }
        }
        if u64::try_from(output.len()).unwrap_or(u64::MAX) != count {
            return Err(DatatypeError::invalid(
                "string range cardinality and enumeration disagree",
            ));
        }
        Ok(output.into_iter().collect())
    }

    fn first_identity(
        &self,
        excluding: &BTreeSet<DataIdentity>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        if !self
            .without_language
            .is_empty_exact(limits.regex, control)?
        {
            let blocked: BTreeSet<_> = excluding
                .iter()
                .filter_map(|identity| match identity {
                    DataIdentity::String {
                        text,
                        language: None,
                    } => Some(text.clone()),
                    _ => None,
                })
                .collect();
            let text = self
                .without_language
                .first_string(&blocked, limits.regex, control)?;
            return Ok(Some(DataIdentity::String {
                text,
                language: None,
            }));
        }
        for rectangle in &self.with_language {
            if rectangle.is_empty(limits, control)? {
                continue;
            }
            let mut skipped_texts = BTreeSet::new();
            for attempt in 0..=excluding.len() {
                poll_index(attempt, limits, control)?;
                let requested = u64::try_from(skipped_texts.len())
                    .unwrap_or(u64::MAX)
                    .saturating_add(1);
                if rectangle
                    .text
                    .cardinality_up_to(requested, limits.regex, control)?
                    < requested
                {
                    break;
                }
                let text = rectangle
                    .text
                    .first_string(&skipped_texts, limits.regex, control)?;
                let blocked_languages: BTreeSet<_> = excluding
                    .iter()
                    .filter_map(|identity| match identity {
                        DataIdentity::String {
                            text: blocked_text,
                            language: Some(language),
                        } if blocked_text == &text => Some(language.clone()),
                        _ => None,
                    })
                    .collect();
                if let Some(language) =
                    rectangle
                        .language
                        .first_tag(&blocked_languages, limits, control)?
                {
                    return Ok(Some(DataIdentity::String {
                        text,
                        language: Some(language),
                    }));
                }
                skipped_texts.insert(text);
            }
        }
        Ok(None)
    }
}

fn check_pattern_state_count(
    observed: usize,
    limits: RangeWireLimits,
) -> Result<(), DatatypeError> {
    let observed = u64::try_from(observed).unwrap_or(u64::MAX);
    if observed > limits.regex.max_pattern_states {
        Err(DatatypeError::resource(
            "max_pattern_states",
            observed,
            limits.regex.max_pattern_states,
        ))
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TagAtom {
    prefix: Vec<String>,
    positive: bool,
}

type TagClause = Vec<TagAtom>;

#[derive(Clone, Debug)]
struct LanguageTagRange {
    clauses: Vec<TagClause>,
}

impl LanguageTagRange {
    fn new(clauses: Vec<TagClause>) -> Self {
        let mut output = Vec::new();
        for clause in clauses {
            if let Some(value) = normalize_tag_clause(clause) {
                if !output.contains(&value) {
                    output.push(value);
                }
            }
        }
        output.sort();
        Self { clauses: output }
    }

    fn all() -> Self {
        Self::new(vec![Vec::new()])
    }

    fn basic(value: &str) -> Result<Self, DatatypeError> {
        if value == "*" {
            return Ok(Self::all());
        }
        let parts: Vec<_> = value.split('-').map(str::to_ascii_lowercase).collect();
        let valid = parts.first().is_some_and(|part| {
            (1..=8).contains(&part.len())
                && part.is_ascii()
                && part
                    .chars()
                    .all(|character| character.is_ascii_alphabetic())
        }) && parts.iter().skip(1).all(|part| {
            (1..=8).contains(&part.len())
                && part.is_ascii()
                && part
                    .chars()
                    .all(|character| character.is_ascii_alphanumeric())
        });
        if !valid {
            return Err(DatatypeError::invalid(
                "rdf:langRange requires an RFC 4647 basic language range",
            ));
        }
        Ok(Self::new(vec![vec![TagAtom {
            prefix: parts,
            positive: true,
        }]]))
    }

    fn contains(&self, value: &str) -> bool {
        if value != value.to_ascii_lowercase() || !is_valid_language_tag(value) {
            return false;
        }
        let parts: Vec<_> = value.split('-').collect();
        self.clauses.iter().any(|clause| {
            clause
                .iter()
                .all(|atom| tag_prefix_matches(&parts, &atom.prefix) == atom.positive)
        })
    }

    fn intersection(&self, other: &Self) -> Self {
        Self::new(
            self.clauses
                .iter()
                .flat_map(|left| {
                    other
                        .clauses
                        .iter()
                        .map(move |right| left.iter().chain(right).cloned().collect())
                })
                .collect(),
        )
    }

    fn complement(&self) -> Self {
        let mut result = vec![Vec::new()];
        for clause in &self.clauses {
            if clause.is_empty() {
                return Self::new(Vec::new());
            }
            let mut next = Vec::new();
            for retained in &result {
                for atom in clause {
                    let mut value = retained.clone();
                    value.push(TagAtom {
                        prefix: atom.prefix.clone(),
                        positive: !atom.positive,
                    });
                    next.push(value);
                }
            }
            result = next;
        }
        Self::new(result)
    }

    fn finite_cardinality(&self) -> Option<BigUint> {
        let mut output = BTreeSet::new();
        for clause in &self.clauses {
            output.extend(finite_tag_clause_values(clause)?);
        }
        Some(BigUint::from(output.len()))
    }

    fn cardinality_up_to(&self, maximum: u64) -> u64 {
        if maximum == 0 {
            return 0;
        }
        match self.finite_cardinality() {
            Some(value) => value.to_u64().unwrap_or(u64::MAX).min(maximum),
            None => maximum,
        }
    }

    fn is_empty(&self) -> bool {
        self.clauses
            .iter()
            .all(|clause| finite_tag_clause_values(clause).is_some_and(|values| values.is_empty()))
    }

    fn enumerate(&self) -> Vec<String> {
        let mut output = BTreeSet::new();
        for clause in &self.clauses {
            if let Some(values) = finite_tag_clause_values(clause) {
                output.extend(values);
            }
        }
        output.into_iter().collect()
    }

    fn first_tag(
        &self,
        excluding: &BTreeSet<String>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<String>, DatatypeError> {
        let work = u64::try_from(excluding.len())
            .unwrap_or(u64::MAX)
            .saturating_add(2);
        if work > limits.ranges.max_witness_steps {
            return Err(DatatypeError::resource(
                "max_witness_steps",
                work,
                limits.ranges.max_witness_steps,
            ));
        }
        control.observe_memory(work.saturating_mul(32))?;
        for (clause_index, clause) in self.clauses.iter().enumerate() {
            poll_index(clause_index, limits, control)?;
            if let Some(values) = finite_tag_clause_values(clause) {
                if let Some(value) = values.into_iter().find(|value| !excluding.contains(value)) {
                    return Ok(Some(value));
                }
                continue;
            }
            let Some(base) = tag_clause_completion(clause) else {
                continue;
            };
            if !excluding.contains(&base) && tag_clause_contains(clause, &base) {
                return Ok(Some(base));
            }
            let count = excluding.len().saturating_add(2);
            for (index, token) in tag_token_candidates(count).into_iter().enumerate() {
                poll_index(index, limits, control)?;
                let candidates = [
                    format!("{base}-{token}"),
                    format!("{base}-x-{token}"),
                    format!("{base}-a-{}", two_character_token(&token)),
                    format!("{base}-{}", variant_token(&token)),
                ];
                if let Some(value) = candidates.into_iter().find(|candidate| {
                    !excluding.contains(candidate)
                        && is_valid_language_tag(candidate)
                        && tag_clause_contains(clause, candidate)
                }) {
                    return Ok(Some(value));
                }
            }
        }
        Ok(None)
    }
}

fn normalize_tag_clause(clause: TagClause) -> Option<TagClause> {
    let mut polarities: BTreeMap<Vec<String>, bool> = BTreeMap::new();
    for atom in clause {
        if polarities
            .get(&atom.prefix)
            .is_some_and(|value| *value != atom.positive)
        {
            return None;
        }
        polarities.insert(atom.prefix, atom.positive);
    }
    let mut positives: Vec<_> = polarities
        .iter()
        .filter(|(_, positive)| **positive)
        .map(|(prefix, _)| prefix.clone())
        .collect();
    positives.sort_by_key(Vec::len);
    let mut required: Option<Vec<String>> = None;
    for prefix in positives {
        if required
            .as_ref()
            .is_some_and(|known| !owned_prefix(known, &prefix))
        {
            return None;
        }
        required = Some(prefix);
    }
    let mut negatives: Vec<_> = polarities
        .iter()
        .filter(|(_, positive)| !**positive)
        .map(|(prefix, _)| prefix.clone())
        .collect();
    negatives.sort_by(|left, right| left.len().cmp(&right.len()).then(left.cmp(right)));
    let mut retained: Vec<Vec<String>> = Vec::new();
    for prefix in negatives {
        if let Some(required) = &required {
            if owned_prefix(&prefix, required) {
                return None;
            }
            if !owned_prefix(required, &prefix) {
                continue;
            }
        }
        if retained.iter().any(|known| owned_prefix(known, &prefix)) {
            continue;
        }
        retained.push(prefix);
    }
    let mut output = required
        .map(|prefix| {
            vec![TagAtom {
                prefix,
                positive: true,
            }]
        })
        .unwrap_or_default();
    output.extend(retained.into_iter().map(|prefix| TagAtom {
        prefix,
        positive: false,
    }));
    Some(output)
}

fn finite_tag_clause_values(clause: &TagClause) -> Option<BTreeSet<String>> {
    let required = clause
        .iter()
        .find(|atom| atom.positive)
        .map(|atom| &atom.prefix);
    let required = required?;
    if required.first().is_some_and(|value| value == "i") {
        return Some(
            I_GRANDFATHERED
                .iter()
                .filter(|value| tag_clause_contains(clause, value))
                .map(|value| (*value).to_owned())
                .collect(),
        );
    }
    if required
        .first()
        .is_some_and(|value| value.len() == 1 && value != "x")
    {
        return Some(BTreeSet::new());
    }
    let joined = required.join("-");
    if IRREGULAR_LEAVES.contains(&joined.as_str()) {
        return Some(if tag_clause_contains(clause, &joined) {
            std::iter::once(joined).collect()
        } else {
            BTreeSet::new()
        });
    }
    if tag_clause_completion(clause).is_some() {
        None
    } else {
        Some(BTreeSet::new())
    }
}

fn tag_clause_completion(clause: &TagClause) -> Option<String> {
    let required = clause.iter().find(|atom| atom.positive);
    let Some(required) = required else {
        let blocked = blocked_tag_children(clause, &[]);
        return tag_token_candidates(blocked.len().saturating_add(2))
            .into_iter()
            .map(|token| two_character_token(&token))
            .find(|candidate| {
                is_valid_language_tag(candidate) && tag_clause_contains(clause, candidate)
            });
    };
    let joined = required.prefix.join("-");
    if is_valid_language_tag(&joined) && tag_clause_contains(clause, &joined) {
        return Some(joined);
    }
    let blocked = blocked_tag_children(clause, &required.prefix);
    for token in tag_token_candidates(blocked.len().saturating_add(2)) {
        if blocked.contains(&token) {
            continue;
        }
        let candidate = format!("{joined}-{token}");
        if is_valid_language_tag(&candidate) && tag_clause_contains(clause, &candidate) {
            return Some(candidate);
        }
    }
    None
}

fn blocked_tag_children(clause: &TagClause, prefix: &[String]) -> BTreeSet<String> {
    clause
        .iter()
        .filter(|atom| {
            !atom.positive
                && atom.prefix.len() == prefix.len().saturating_add(1)
                && owned_prefix(prefix, &atom.prefix)
        })
        .map(|atom| atom.prefix[prefix.len()].clone())
        .collect()
}

fn tag_token_candidates(count: usize) -> Vec<String> {
    let mut output = Vec::new();
    for index in 0..count.max(8) {
        let encoded = base36(index);
        output.push(last_ascii(&encoded, 8));
        output.push(two_character_token(&encoded));
        output.push(last_ascii(&format!("aaaa{encoded}"), 4));
        output.push(last_ascii(&format!("aaaa{encoded}"), 5));
    }
    output
}

fn base36(mut value: usize) -> String {
    const DIGITS: &[u8; 36] = b"abcdefghijklmnopqrstuvwxyz0123456789";
    let mut reversed = Vec::new();
    loop {
        let remainder = value % DIGITS.len();
        reversed.push(char::from(DIGITS[remainder]));
        value /= DIGITS.len();
        if value == 0 {
            reversed.reverse();
            return reversed.into_iter().collect();
        }
    }
}

fn two_character_token(value: &str) -> String {
    if value.len() < 2 {
        last_ascii(&format!("a{value}"), 2)
    } else {
        last_ascii(value, 2)
    }
}

fn variant_token(value: &str) -> String {
    last_ascii(&format!("aaaa{value}"), 5)
}

fn last_ascii(value: &str, maximum: usize) -> String {
    let start = value.len().saturating_sub(maximum);
    value[start..].to_owned()
}

fn tag_clause_contains(clause: &TagClause, value: &str) -> bool {
    let parts: Vec<_> = value.split('-').collect();
    clause
        .iter()
        .all(|atom| tag_prefix_matches(&parts, &atom.prefix) == atom.positive)
}

fn tag_prefix_matches(parts: &[&str], prefix: &[String]) -> bool {
    prefix.len() <= parts.len() && prefix.iter().zip(parts).all(|(left, right)| left == right)
}

fn owned_prefix(left: &[String], right: &[String]) -> bool {
    left.len() <= right.len()
        && left
            .iter()
            .zip(right)
            .all(|(first, second)| first == second)
}

const I_GRANDFATHERED: [&str; 13] = [
    "i-ami",
    "i-bnn",
    "i-default",
    "i-enochian",
    "i-hak",
    "i-klingon",
    "i-lux",
    "i-mingo",
    "i-navajo",
    "i-pwn",
    "i-tao",
    "i-tay",
    "i-tsu",
];

const IRREGULAR_LEAVES: [&str; 4] = ["en-gb-oed", "sgn-be-fr", "sgn-be-nl", "sgn-ch-de"];

const GRANDFATHERED: [&str; 26] = [
    "art-lojban",
    "cel-gaulish",
    "en-gb-oed",
    "i-ami",
    "i-bnn",
    "i-default",
    "i-enochian",
    "i-hak",
    "i-klingon",
    "i-lux",
    "i-mingo",
    "i-navajo",
    "i-pwn",
    "i-tao",
    "i-tay",
    "i-tsu",
    "no-bok",
    "no-nyn",
    "sgn-be-fr",
    "sgn-be-nl",
    "sgn-ch-de",
    "zh-guoyu",
    "zh-hakka",
    "zh-min",
    "zh-min-nan",
    "zh-xiang",
];

fn is_valid_language_tag(language: &str) -> bool {
    if language.is_empty()
        || !language.is_ascii()
        || language != language.to_ascii_lowercase()
        || language.split('-').any(str::is_empty)
    {
        return false;
    }
    if GRANDFATHERED.contains(&language) {
        return true;
    }
    let parts: Vec<_> = language.split('-').collect();
    if parts[0] == "x" {
        return parts.len() >= 2
            && parts[1..].iter().all(|part| {
                (1..=8).contains(&part.len())
                    && part
                        .chars()
                        .all(|character| character.is_ascii_alphanumeric())
            });
    }
    let first = parts[0];
    if !(first
        .chars()
        .all(|character| character.is_ascii_alphabetic())
        && (2..=8).contains(&first.len()))
    {
        return false;
    }
    let mut index = 1;
    if matches!(first.len(), 2 | 3) {
        let mut count = 0;
        while index < parts.len()
            && parts[index].len() == 3
            && parts[index]
                .chars()
                .all(|character| character.is_ascii_alphabetic())
            && count < 3
        {
            index += 1;
            count += 1;
        }
    }
    if index < parts.len()
        && parts[index].len() == 4
        && parts[index]
            .chars()
            .all(|character| character.is_ascii_alphabetic())
    {
        index += 1;
    }
    if index < parts.len()
        && ((parts[index].len() == 2
            && parts[index]
                .chars()
                .all(|character| character.is_ascii_alphabetic()))
            || (parts[index].len() == 3
                && parts[index]
                    .chars()
                    .all(|character| character.is_ascii_digit())))
    {
        index += 1;
    }
    let mut variants = HashSet::new();
    while index < parts.len()
        && ((5..=8).contains(&parts[index].len())
            || (parts[index].len() == 4 && parts[index].as_bytes()[0].is_ascii_digit()))
        && parts[index]
            .chars()
            .all(|character| character.is_ascii_alphanumeric())
    {
        if !variants.insert(parts[index]) {
            return false;
        }
        index += 1;
    }
    let mut singletons = HashSet::new();
    while index < parts.len() && parts[index].len() == 1 && parts[index] != "x" {
        if !parts[index]
            .chars()
            .all(|character| character.is_ascii_alphanumeric())
            || !singletons.insert(parts[index])
        {
            return false;
        }
        index += 1;
        let start = index;
        while index < parts.len()
            && (2..=8).contains(&parts[index].len())
            && parts[index]
                .chars()
                .all(|character| character.is_ascii_alphanumeric())
        {
            index += 1;
        }
        if index == start {
            return false;
        }
    }
    if index < parts.len() && parts[index] == "x" {
        index += 1;
        let start = index;
        while index < parts.len()
            && (1..=8).contains(&parts[index].len())
            && parts[index]
                .chars()
                .all(|character| character.is_ascii_alphanumeric())
        {
            index += 1;
        }
        if index == start {
            return false;
        }
    }
    index == parts.len()
}

pub(crate) fn is_supported_datatype(iri: &str) -> bool {
    iri == RDFS_LITERAL
        || numeric_datatype_spec(iri).is_some()
        || matches!(
            iri,
            XSD_BOOLEAN
                | XSD_FLOAT
                | XSD_DOUBLE
                | XSD_STRING
                | XSD_NORMALIZED_STRING
                | XSD_TOKEN
                | XSD_LANGUAGE
                | XSD_NAME
                | XSD_NCNAME
                | XSD_NMTOKEN
                | RDF_PLAIN_LITERAL
                | XSD_HEX_BINARY
                | XSD_BASE64_BINARY
                | XSD_ANY_URI
                | RDF_XML_LITERAL
                | XSD_DATE_TIME
                | XSD_DATE_TIME_STAMP
        )
}

const fn identity_family(value: &DataIdentity) -> Family {
    match value {
        DataIdentity::Numeric(_) => Family::Numeric,
        DataIdentity::Boolean(_) => Family::Boolean,
        DataIdentity::IEEE {
            format: IEEEFormat::Float32,
            ..
        } => Family::Float,
        DataIdentity::IEEE {
            format: IEEEFormat::Float64,
            ..
        } => Family::Double,
        DataIdentity::String { .. } => Family::String,
        DataIdentity::Binary {
            kind: BinaryKind::Hex,
            ..
        } => Family::HexBinary,
        DataIdentity::Binary {
            kind: BinaryKind::Base64,
            ..
        } => Family::Base64Binary,
        DataIdentity::Uri(_) => Family::Uri,
        DataIdentity::Xml(_) => Family::Xml,
        DataIdentity::DateTime { .. } => Family::DateTime,
    }
}

#[derive(Clone, Copy)]
struct NumericSpec {
    domain: NumericDomain,
    lower: Option<i128>,
    upper: Option<u128>,
    upper_signed: Option<i128>,
}

fn numeric_datatype_spec(iri: &str) -> Option<NumericSpec> {
    let unbounded = |domain| NumericSpec {
        domain,
        lower: None,
        upper: None,
        upper_signed: None,
    };
    Some(match iri {
        OWL_REAL => unbounded(NumericDomain::Real),
        OWL_RATIONAL => unbounded(NumericDomain::Rational),
        XSD_DECIMAL => unbounded(NumericDomain::Decimal),
        XSD_INTEGER => unbounded(NumericDomain::Integer),
        value if value == format!("{XSD}nonNegativeInteger") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(0),
            upper: None,
            upper_signed: None,
        },
        value if value == format!("{XSD}positiveInteger") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(1),
            upper: None,
            upper_signed: None,
        },
        value if value == format!("{XSD}nonPositiveInteger") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: None,
            upper: None,
            upper_signed: Some(0),
        },
        value if value == format!("{XSD}negativeInteger") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: None,
            upper: None,
            upper_signed: Some(-1),
        },
        value if value == format!("{XSD}long") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(i128::from(i64::MIN)),
            upper: None,
            upper_signed: Some(i128::from(i64::MAX)),
        },
        value if value == format!("{XSD}int") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(i128::from(i32::MIN)),
            upper: None,
            upper_signed: Some(i128::from(i32::MAX)),
        },
        value if value == format!("{XSD}short") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(i128::from(i16::MIN)),
            upper: None,
            upper_signed: Some(i128::from(i16::MAX)),
        },
        value if value == format!("{XSD}byte") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(i128::from(i8::MIN)),
            upper: None,
            upper_signed: Some(i128::from(i8::MAX)),
        },
        value if value == format!("{XSD}unsignedLong") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(0),
            upper: Some(u128::from(u64::MAX)),
            upper_signed: None,
        },
        value if value == format!("{XSD}unsignedInt") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(0),
            upper: Some(u128::from(u32::MAX)),
            upper_signed: None,
        },
        value if value == format!("{XSD}unsignedShort") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(0),
            upper: Some(u128::from(u16::MAX)),
            upper_signed: None,
        },
        value if value == format!("{XSD}unsignedByte") => NumericSpec {
            domain: NumericDomain::Integer,
            lower: Some(0),
            upper: Some(u128::from(u8::MAX)),
            upper_signed: None,
        },
        _ => return None,
    })
}

fn compile_atom(
    expression: &RangeExpression,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Atom, DatatypeError> {
    let payload = match expression.kind {
        ExpressionKind::Enumeration => AtomPayload::Enumeration(
            expression
                .values
                .iter()
                .map(|value| value.identity.clone())
                .collect(),
        ),
        ExpressionKind::Datatype | ExpressionKind::Restriction => {
            let iri = expression
                .datatype_iri
                .as_deref()
                .ok_or_else(|| DatatypeError::invalid("data-range atom has no datatype IRI"))?;
            if iri == RDFS_LITERAL {
                if expression.kind == ExpressionKind::Restriction {
                    return Err(DatatypeError::invalid(
                        "facets are not legal on rdfs:Literal",
                    ));
                }
                AtomPayload::Universal
            } else {
                let mut range = range_for_datatype(iri, limits, control)?;
                if expression.kind == ExpressionKind::Restriction {
                    for (index, facet) in expression.facets.iter().enumerate() {
                        poll_index(index, limits, control)?;
                        range = apply_facet(iri, range, facet, limits, control)?;
                    }
                }
                AtomPayload::Family(range)
            }
        }
        _ => {
            return Err(DatatypeError::invalid(
                "only datatype, restriction, and enumeration expressions are atoms",
            ));
        }
    };
    Ok(Atom {
        canonical: expression.canonical.clone(),
        payload,
    })
}

fn range_for_datatype(
    iri: &str,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<FamilyRange, DatatypeError> {
    if let Some(spec) = numeric_datatype_spec(iri) {
        let lower = spec
            .lower
            .map(|value| exact_integer(BigInt::from(value)))
            .transpose()?;
        let upper = match (spec.upper, spec.upper_signed) {
            (Some(value), None) => Some(exact_integer(BigInt::from(value))?),
            (None, Some(value)) => Some(exact_integer(BigInt::from(value))?),
            (None, None) => None,
            _ => return Err(DatatypeError::invalid("numeric datatype bounds conflict")),
        };
        return Ok(FamilyRange::Numeric(NumericRange::between(
            spec.domain,
            lower.clone(),
            lower.is_some(),
            upper.clone(),
            upper.is_some(),
        )?));
    }
    Ok(match iri {
        XSD_BOOLEAN => FamilyRange::Boolean(BooleanRange::all()),
        XSD_FLOAT => FamilyRange::Ieee(IEEERange::all(IEEEFormat::Float32)?),
        XSD_DOUBLE => FamilyRange::Ieee(IEEERange::all(IEEEFormat::Float64)?),
        XSD_STRING
        | XSD_NORMALIZED_STRING
        | XSD_TOKEN
        | XSD_LANGUAGE
        | XSD_NAME
        | XSD_NCNAME
        | XSD_NMTOKEN
        | RDF_PLAIN_LITERAL => {
            FamilyRange::String(StringFamilyRange::for_datatype(iri, limits, control)?)
        }
        XSD_HEX_BINARY => FamilyRange::Binary(BinaryRange::all(BinaryKind::Hex)),
        XSD_BASE64_BINARY => FamilyRange::Binary(BinaryRange::all(BinaryKind::Base64)),
        XSD_ANY_URI => FamilyRange::Uri(RegexRange::all()),
        RDF_XML_LITERAL => FamilyRange::Xml(true),
        XSD_DATE_TIME => FamilyRange::DateTime(DateTimeRange::all(false)),
        XSD_DATE_TIME_STAMP => FamilyRange::DateTime(DateTimeRange::all(true)),
        _ => return Err(unsupported_datatype(iri)),
    })
}

fn exact_integer(value: BigInt) -> Result<ExactRational, DatatypeError> {
    ExactRational::new(value, BigInt::one())
}

fn ordered_facet(value: &str) -> Option<OrderedFacet> {
    match value {
        XSD_MIN_INCLUSIVE => Some(OrderedFacet::MinInclusive),
        XSD_MIN_EXCLUSIVE => Some(OrderedFacet::MinExclusive),
        XSD_MAX_INCLUSIVE => Some(OrderedFacet::MaxInclusive),
        XSD_MAX_EXCLUSIVE => Some(OrderedFacet::MaxExclusive),
        _ => None,
    }
}

fn length_facet(value: &str) -> Option<LengthFacet> {
    match value {
        XSD_LENGTH => Some(LengthFacet::Length),
        XSD_MIN_LENGTH => Some(LengthFacet::MinLength),
        XSD_MAX_LENGTH => Some(LengthFacet::MaxLength),
        _ => None,
    }
}

fn apply_facet(
    iri: &str,
    range: FamilyRange,
    facet: &DecodedFacet,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<FamilyRange, DatatypeError> {
    if numeric_datatype_spec(iri).is_some() {
        let selected =
            ordered_facet(&facet.facet_iri).ok_or_else(|| illegal_facet(iri, &facet.facet_iri))?;
        let ComparisonValue::Numeric(boundary) = &facet.value.comparison else {
            return Err(invalid_facet_value(iri, &facet.facet_iri));
        };
        let FamilyRange::Numeric(value) = range else {
            return Err(DatatypeError::invalid(
                "numeric facet range has wrong family",
            ));
        };
        return Ok(FamilyRange::Numeric(
            value.apply_facet(selected, boundary.clone())?,
        ));
    }
    match iri {
        XSD_FLOAT | XSD_DOUBLE => {
            let selected = ordered_facet(&facet.facet_iri)
                .ok_or_else(|| illegal_facet(iri, &facet.facet_iri))?;
            let expected = if iri == XSD_FLOAT {
                IEEEFormat::Float32
            } else {
                IEEEFormat::Float64
            };
            if !matches!(
                facet.value.comparison,
                ComparisonValue::IEEE { format, .. } if format == expected
            ) {
                return Err(invalid_facet_value(iri, &facet.facet_iri));
            }
            let DataIdentity::IEEE { format, bits } = facet.value.identity else {
                return Err(invalid_facet_value(iri, &facet.facet_iri));
            };
            if format != expected {
                return Err(invalid_facet_value(iri, &facet.facet_iri));
            }
            let FamilyRange::Ieee(value) = range else {
                return Err(DatatypeError::invalid("IEEE facet range has wrong family"));
            };
            Ok(FamilyRange::Ieee(value.apply_facet(selected, bits)?))
        }
        XSD_HEX_BINARY | XSD_BASE64_BINARY => {
            let selected = length_facet(&facet.facet_iri)
                .ok_or_else(|| illegal_facet(iri, &facet.facet_iri))?;
            let boundary = length_boundary(iri, facet)?;
            let FamilyRange::Binary(value) = range else {
                return Err(DatatypeError::invalid(
                    "binary facet range has wrong family",
                ));
            };
            Ok(FamilyRange::Binary(value.apply_facet(selected, boundary)))
        }
        XSD_STRING
        | XSD_NORMALIZED_STRING
        | XSD_TOKEN
        | XSD_LANGUAGE
        | XSD_NAME
        | XSD_NCNAME
        | XSD_NMTOKEN
        | RDF_PLAIN_LITERAL => {
            let FamilyRange::String(value) = range else {
                return Err(DatatypeError::invalid(
                    "string facet range has wrong family",
                ));
            };
            if let Some(selected) = length_facet(&facet.facet_iri) {
                let boundary = length_boundary(iri, facet)?;
                let (minimum, maximum) = match selected {
                    LengthFacet::Length => (boundary, Some(boundary)),
                    LengthFacet::MinLength => (boundary, None),
                    LengthFacet::MaxLength => (0, Some(boundary)),
                };
                let pattern = XsdRegex::length_range(minimum, maximum, limits.regex, control)?;
                return Ok(FamilyRange::String(value.with_text_pattern(&pattern)));
            }
            let text = untagged_string_facet(iri, facet)?;
            if facet.facet_iri == XSD_PATTERN {
                let pattern = XsdRegex::compile(text, limits.regex, control)?;
                Ok(FamilyRange::String(value.with_text_pattern(&pattern)))
            } else if facet.facet_iri == RDF_LANG_RANGE && iri == RDF_PLAIN_LITERAL {
                Ok(FamilyRange::String(
                    value.with_language(&LanguageTagRange::basic(text)?),
                ))
            } else {
                Err(illegal_facet(iri, &facet.facet_iri))
            }
        }
        XSD_ANY_URI => {
            let FamilyRange::Uri(value) = range else {
                return Err(DatatypeError::invalid("URI facet range has wrong family"));
            };
            let pattern = if let Some(selected) = length_facet(&facet.facet_iri) {
                let boundary = length_boundary(iri, facet)?;
                let (minimum, maximum) = match selected {
                    LengthFacet::Length => (boundary, Some(boundary)),
                    LengthFacet::MinLength => (boundary, None),
                    LengthFacet::MaxLength => (0, Some(boundary)),
                };
                XsdRegex::length_range(minimum, maximum, limits.regex, control)?
            } else if facet.facet_iri == XSD_PATTERN {
                XsdRegex::compile(untagged_string_facet(iri, facet)?, limits.regex, control)?
            } else {
                return Err(illegal_facet(iri, &facet.facet_iri));
            };
            Ok(FamilyRange::Uri(RegexRange {
                universe: value.universe,
                language: value.language.intersection(&pattern),
            }))
        }
        XSD_DATE_TIME | XSD_DATE_TIME_STAMP => {
            let selected = ordered_facet(&facet.facet_iri)
                .ok_or_else(|| illegal_facet(iri, &facet.facet_iri))?;
            let ComparisonValue::DateTime {
                local,
                timezone_offset_minutes,
            } = &facet.value.comparison
            else {
                return Err(invalid_facet_value(iri, &facet.facet_iri));
            };
            let FamilyRange::DateTime(value) = range else {
                return Err(DatatypeError::invalid(
                    "date/time facet range has wrong family",
                ));
            };
            let restriction = date_time_bound(
                iri == XSD_DATE_TIME_STAMP,
                selected,
                local,
                *timezone_offset_minutes,
            )?;
            Ok(FamilyRange::DateTime(value.intersection(&restriction)?))
        }
        XSD_BOOLEAN | RDF_XML_LITERAL | RDFS_LITERAL => Err(illegal_facet(iri, &facet.facet_iri)),
        _ => Err(unsupported_datatype(iri)),
    }
}

fn date_time_bound(
    require_timezone: bool,
    facet: OrderedFacet,
    local: &ExactRational,
    timezone: Option<i16>,
) -> Result<DateTimeRange, DatatypeError> {
    let bound_is_zoned = timezone.is_some();
    let base = timezone.map_or_else(
        || local.clone(),
        |offset| local.subtract_integer(i64::from(offset) * 60),
    );
    let lower = matches!(
        facet,
        OrderedFacet::MinInclusive | OrderedFacet::MinExclusive
    );
    let inclusive = matches!(
        facet,
        OrderedFacet::MinInclusive | OrderedFacet::MaxInclusive
    );
    let (zoned_endpoint, unzoned_endpoint) = match (lower, bound_is_zoned) {
        (true, true) => (base.clone(), base.subtract_integer(-50_400)),
        (true, false) => (base.subtract_integer(-50_400), base),
        (false, true) => (base.clone(), base.subtract_integer(50_400)),
        (false, false) => (base.subtract_integer(50_400), base),
    };
    let zoned_inclusive = inclusive && bound_is_zoned;
    let unzoned_inclusive = inclusive && !bound_is_zoned;
    Ok(DateTimeRange {
        zoned: if lower {
            NumericRange::between(
                NumericDomain::Real,
                Some(zoned_endpoint),
                zoned_inclusive,
                None,
                false,
            )?
        } else {
            NumericRange::between(
                NumericDomain::Real,
                None,
                false,
                Some(zoned_endpoint),
                zoned_inclusive,
            )?
        },
        unzoned: if require_timezone {
            NumericRange::empty(NumericDomain::Real)
        } else if lower {
            NumericRange::between(
                NumericDomain::Real,
                Some(unzoned_endpoint),
                unzoned_inclusive,
                None,
                false,
            )?
        } else {
            NumericRange::between(
                NumericDomain::Real,
                None,
                false,
                Some(unzoned_endpoint),
                unzoned_inclusive,
            )?
        },
        include_unzoned: true,
    })
}

fn length_boundary(iri: &str, facet: &DecodedFacet) -> Result<u64, DatatypeError> {
    let DataIdentity::Numeric(value) = &facet.value.identity else {
        return Err(invalid_facet_value(iri, &facet.facet_iri));
    };
    if value.denominator_token() != "+1" {
        return Err(invalid_facet_value(iri, &facet.facet_iri));
    }
    let token = value.numerator_token();
    if token.starts_with('-') {
        return Err(invalid_facet_value(iri, &facet.facet_iri));
    }
    u64::from_str_radix(token.strip_prefix('+').unwrap_or(&token), 16)
        .map_err(|_| DatatypeError::resource("max_length_boundary", u64::MAX, u64::MAX - 1))
}

fn untagged_string_facet<'a>(iri: &str, facet: &'a DecodedFacet) -> Result<&'a str, DatatypeError> {
    let DataIdentity::String {
        text,
        language: None,
    } = &facet.value.identity
    else {
        return Err(invalid_facet_value(iri, &facet.facet_iri));
    };
    Ok(text)
}

fn illegal_facet(iri: &str, facet: &str) -> DatatypeError {
    DatatypeError::invalid(format!(
        "facet is not legal for the restricted OWL datatype: {iri} / {facet}"
    ))
}

fn invalid_facet_value(iri: &str, facet: &str) -> DatatypeError {
    DatatypeError::invalid(format!(
        "facet literal has the wrong datatype or value domain: {iri} / {facet}"
    ))
}

#[derive(Clone, Debug)]
struct FamilySubset {
    family: Family,
    base: FamilyRange,
    numeric_exclusions: Vec<NumericRange>,
    finite_exclusions: BTreeSet<DataIdentity>,
}

impl FamilySubset {
    fn contains(
        &self,
        identity: &DataIdentity,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        if identity_family(identity) != self.family || self.finite_exclusions.contains(identity) {
            return Ok(false);
        }
        if !self.base.contains(identity, limits, control)? {
            return Ok(false);
        }
        let DataIdentity::Numeric(value) = identity else {
            return Ok(true);
        };
        for exclusion in &self.numeric_exclusions {
            if exclusion.contains(value)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn cardinality(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Cardinality, DatatypeError> {
        if self.base.is_empty(limits, control)? {
            return Ok(Cardinality::Empty);
        }
        let cardinality = self.base.cardinality(limits, control)?;
        if cardinality == Cardinality::Infinite {
            return Ok(Cardinality::Infinite);
        }
        if !self.numeric_exclusions.is_empty() {
            let values = self.base.enumerate(limits, control)?;
            let mut retained = BigUint::zero();
            for value in values {
                if self.contains(&value, limits, control)? {
                    retained += BigUint::one();
                }
            }
            return Ok(cardinality_from_count(retained));
        }
        let mut count = finite_count(cardinality);
        for identity in &self.finite_exclusions {
            if identity_family(identity) == self.family
                && self.base.contains(identity, limits, control)?
            {
                count -= BigUint::one();
            }
        }
        Ok(cardinality_from_count(count))
    }

    fn is_nonempty(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        if self.base.is_empty(limits, control)? {
            return Ok(false);
        }
        if !self.numeric_exclusions.is_empty() {
            if self.base.cardinality(limits, control)? == Cardinality::Infinite {
                return Ok(true);
            }
            for identity in self.base.enumerate(limits, control)? {
                if self.contains(&identity, limits, control)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        let removed = u64::try_from(self.finite_exclusions.len()).unwrap_or(u64::MAX);
        let maximum = removed.saturating_add(1);
        let base_count = self.base.cardinality_up_to(maximum, limits, control)?;
        if base_count == maximum {
            return Ok(true);
        }
        let mut actual_removed = 0_u64;
        for identity in &self.finite_exclusions {
            if identity_family(identity) == self.family
                && self.base.contains(identity, limits, control)?
            {
                actual_removed = actual_removed.saturating_add(1);
            }
        }
        Ok(base_count > actual_removed)
    }

    fn cardinality_up_to(
        &self,
        maximum: u64,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<u64, DatatypeError> {
        if maximum == 0 || self.base.is_empty(limits, control)? {
            return Ok(0);
        }
        if !self.numeric_exclusions.is_empty() {
            if self.base.cardinality(limits, control)? == Cardinality::Infinite {
                return Ok(maximum);
            }
            let mut retained = 0_u64;
            for identity in self.base.enumerate(limits, control)? {
                if self.contains(&identity, limits, control)? {
                    retained = retained.saturating_add(1);
                    if retained == maximum {
                        return Ok(maximum);
                    }
                }
            }
            return Ok(retained);
        }
        let exclusion_bound = u64::try_from(self.finite_exclusions.len()).unwrap_or(u64::MAX);
        let requested = maximum.saturating_add(exclusion_bound);
        let base_count = self.base.cardinality_up_to(requested, limits, control)?;
        if base_count == requested {
            return Ok(maximum);
        }
        let mut removed = 0_u64;
        for identity in &self.finite_exclusions {
            if identity_family(identity) == self.family
                && self.base.contains(identity, limits, control)?
            {
                removed = removed.saturating_add(1);
            }
        }
        Ok(base_count.saturating_sub(removed).min(maximum))
    }

    fn first_identity(
        &self,
        excluding: &BTreeSet<DataIdentity>,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        let family_exclusions: BTreeSet<_> = excluding
            .iter()
            .filter(|value| identity_family(value) == self.family)
            .cloned()
            .chain(self.finite_exclusions.iter().cloned())
            .collect();
        let enumeration_cap = limits.ranges.max_enumeration_values.saturating_add(1);
        let cardinality = self.cardinality_up_to(enumeration_cap, limits, control)?;
        if cardinality <= limits.ranges.max_enumeration_values {
            for identity in self.enumerate(limits, control)? {
                if !family_exclusions.contains(&identity) {
                    return Ok(Some(identity));
                }
            }
            return Ok(None);
        }
        let candidate = self.base.first_identity(
            &family_exclusions,
            &self.numeric_exclusions,
            limits,
            control,
        )?;
        let Some(candidate) = candidate else {
            return Ok(None);
        };
        if self.contains(&candidate, limits, control)? && !family_exclusions.contains(&candidate) {
            Ok(Some(candidate))
        } else {
            Ok(None)
        }
    }

    fn enumerate(
        &self,
        limits: RangeWireLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        materializable_count(
            &self.cardinality(limits, control)?,
            limits.ranges.max_enumeration_values,
        )?;
        self.base
            .enumerate(limits, control)?
            .into_iter()
            .filter_map(|identity| match self.contains(&identity, limits, control) {
                Ok(true) => Some(Ok(identity)),
                Ok(false) => None,
                Err(error) => Some(Err(error)),
            })
            .collect::<Result<Vec<_>, _>>()
    }
}

fn clause_nonempty(
    clause: &Clause,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<bool, DatatypeError> {
    if let Some(values) = explicit_candidates(clause, limits, control)? {
        return Ok(!values.is_empty());
    }
    for subset in clause_family_subsets(clause, limits, control)? {
        if subset.is_nonempty(limits, control)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn clause_cardinality(
    clause: &Clause,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Cardinality, DatatypeError> {
    if let Some(values) = explicit_candidates(clause, limits, control)? {
        return Ok(cardinality_from_count(BigUint::from(values.len())));
    }
    let subsets = clause_family_subsets(clause, limits, control)?;
    let mut total = BigUint::zero();
    for subset in subsets {
        match subset.cardinality(limits, control)? {
            Cardinality::Empty => {}
            Cardinality::Finite(value) => total += value,
            Cardinality::Infinite => return Ok(Cardinality::Infinite),
        }
    }
    Ok(cardinality_from_count(total))
}

fn clause_cardinality_up_to(
    clause: &Clause,
    maximum: u64,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<u64, DatatypeError> {
    if maximum == 0 {
        return Ok(0);
    }
    if let Some(values) = explicit_candidates(clause, limits, control)? {
        return Ok(u64::try_from(values.len()).unwrap_or(u64::MAX).min(maximum));
    }
    let mut total = 0_u64;
    for subset in clause_family_subsets(clause, limits, control)? {
        total = total.saturating_add(subset.cardinality_up_to(maximum - total, limits, control)?);
        if total == maximum {
            return Ok(maximum);
        }
    }
    Ok(total)
}

fn enumerate_clause(
    clause: &Clause,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Vec<DataIdentity>, DatatypeError> {
    if let Some(values) = explicit_candidates(clause, limits, control)? {
        return Ok(values);
    }
    let mut output = Vec::new();
    for subset in clause_family_subsets(clause, limits, control)? {
        output.extend(subset.enumerate(limits, control)?);
        let observed = u64::try_from(output.len()).unwrap_or(u64::MAX);
        if observed > limits.ranges.max_enumeration_values {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                observed,
                limits.ranges.max_enumeration_values,
            ));
        }
    }
    Ok(output)
}

fn explicit_candidates(
    clause: &Clause,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Option<Vec<DataIdentity>>, DatatypeError> {
    let mut positives = clause.iter().filter_map(|atom| match &atom.atom.payload {
        AtomPayload::Enumeration(values) if atom.positive => Some(values),
        _ => None,
    });
    let Some(first) = positives.next() else {
        return Ok(None);
    };
    let mut candidates = first.clone();
    for values in positives {
        candidates = candidates.intersection(values).cloned().collect();
    }
    let mut retained = Vec::new();
    for (index, identity) in candidates.into_iter().enumerate() {
        poll_index(index, limits, control)?;
        let mut matches = true;
        for atom in clause {
            if atom.atom.contains(&identity, limits, control)? != atom.positive {
                matches = false;
                break;
            }
        }
        if matches {
            retained.push(identity);
        }
    }
    Ok(Some(retained))
}

fn clause_family_subsets(
    clause: &Clause,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<Vec<FamilySubset>, DatatypeError> {
    let mut positive_families = BTreeSet::new();
    for atom in clause {
        if atom.positive {
            if let AtomPayload::Family(range) = &atom.atom.payload {
                positive_families.insert(range.family());
            }
        }
    }
    if positive_families.len() > 1 {
        return Ok(Vec::new());
    }
    let families: Vec<_> = if positive_families.is_empty() {
        FAMILIES.to_vec()
    } else {
        positive_families.into_iter().collect()
    };
    let negative_values: BTreeSet<_> = clause
        .iter()
        .filter(|atom| !atom.positive)
        .filter_map(|atom| match &atom.atom.payload {
            AtomPayload::Enumeration(values) => Some(values),
            _ => None,
        })
        .flat_map(BTreeSet::iter)
        .cloned()
        .collect();
    let mut output = Vec::new();
    for (index, family) in families.into_iter().enumerate() {
        poll_index(index, limits, control)?;
        let mut base = family_universe(family, limits, control)?;
        for atom in clause {
            if !atom.positive {
                continue;
            }
            if let AtomPayload::Family(value) = &atom.atom.payload {
                if value.family() == family {
                    base = base.intersection(value)?;
                    check_family_complexity(&base, limits, control)?;
                }
            }
        }
        let mut numeric_exclusions = Vec::new();
        for atom in clause {
            if atom.positive {
                continue;
            }
            if let AtomPayload::Family(value) = &atom.atom.payload {
                if value.family() != family {
                    continue;
                }
                match (&base, value) {
                    (FamilyRange::Numeric(current), FamilyRange::Numeric(exclusion))
                        if exclusion.domain() < current.domain() =>
                    {
                        numeric_exclusions.push(exclusion.clone());
                    }
                    _ => {
                        let complement = value.complement()?;
                        check_family_complexity(&complement, limits, control)?;
                        base = base.intersection(&complement)?;
                        check_family_complexity(&base, limits, control)?;
                    }
                }
            }
        }
        output.push(FamilySubset {
            family,
            base,
            numeric_exclusions,
            finite_exclusions: negative_values
                .iter()
                .filter(|value| identity_family(value) == family)
                .cloned()
                .collect(),
        });
    }
    Ok(output)
}

fn check_family_complexity(
    range: &FamilyRange,
    limits: RangeWireLimits,
    control: &impl DatatypeControl,
) -> Result<(), DatatypeError> {
    if let FamilyRange::String(value) = range {
        check_pattern_state_count(value.with_language.len(), limits)?;
        let tag_states = value
            .with_language
            .iter()
            .map(|rectangle| {
                rectangle.language.clauses.len()
                    + rectangle
                        .language
                        .clauses
                        .iter()
                        .map(Vec::len)
                        .sum::<usize>()
            })
            .sum::<usize>();
        check_pattern_state_count(tag_states, limits)?;
    }
    control.poll()
}

fn family_universe(
    family: Family,
    _limits: RangeWireLimits,
    _control: &impl DatatypeControl,
) -> Result<FamilyRange, DatatypeError> {
    Ok(match family {
        Family::Numeric => FamilyRange::Numeric(NumericRange::all(NumericDomain::Real)),
        Family::Boolean => FamilyRange::Boolean(BooleanRange::all()),
        Family::Float => FamilyRange::Ieee(IEEERange::all(IEEEFormat::Float32)?),
        Family::Double => FamilyRange::Ieee(IEEERange::all(IEEEFormat::Float64)?),
        Family::String => FamilyRange::String(StringFamilyRange::all()),
        Family::HexBinary => FamilyRange::Binary(BinaryRange::all(BinaryKind::Hex)),
        Family::Base64Binary => FamilyRange::Binary(BinaryRange::all(BinaryKind::Base64)),
        Family::Uri => FamilyRange::Uri(RegexRange::all()),
        Family::Xml => FamilyRange::Xml(true),
        Family::DateTime => FamilyRange::DateTime(DateTimeRange::all(false)),
    })
}

#[cfg(test)]
#[path = "range_wire_tests.rs"]
mod range_wire_tests;
