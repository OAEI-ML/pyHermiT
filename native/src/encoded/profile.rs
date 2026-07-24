//! Bounded OWL 2 DL profile diagnostics over encoded structural input.
//!
//! Profile violations are successful semantic output. Malformed columns,
//! resource exhaustion, and cancellation remain distinct operational failures.
//! This first private phase owns exact data-arity, top-data-property, local
//! anonymous-placement, and extension projections. Structural-columns schema 1
//! does not carry document-origin rows, so the manifest exposes canonical root
//! provenance without inventing `ProfileIssue.document_keys`. Anonymous graph
//! facts remain private until all selected slices can be merged and validated
//! globally. Issue ordering and deduplication use the exact projected field
//! tuple published by this phase.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::borrow::Cow;
use std::convert::Infallible;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::canonical::{self, AnonymousScopeMap, CanonicalBudget};
use super::model::{
    ComponentKind, ComponentRef, ComponentValue, NodeId, RootKind, ScalarRef, ValidatedModel,
};
use super::symbols::RootHandler;
use super::{u32_at, ByteSource, EncodedResult, EncodedValidationError};

const PROFILE_PHASE_SCHEMA_VERSION: u16 = 1;
const POSTINGS_ALL: u8 = 0;
const POSTINGS_INCLUDE: u8 = 1;
const POSTINGS_EXCLUDE: u8 = 2;
const IRI_TAG: u16 = 1;
const ENTITY_TAG: u16 = 2;
const ANONYMOUS_INDIVIDUAL_TAG: u16 = 3;
const OBJECT_ONE_OF_TAG: u16 = 33;
const OBJECT_HAS_VALUE_TAG: u16 = 36;
const DATA_SOME_VALUES_FROM_TAG: u16 = 41;
const DATA_ALL_VALUES_FROM_TAG: u16 = 42;
const DECLARATION_TAG: u16 = 60;
const SUB_DATA_PROPERTY_TAG: u16 = 90;
const SAME_INDIVIDUAL_TAG: u16 = 110;
const DIFFERENT_INDIVIDUALS_TAG: u16 = 111;
const OBJECT_PROPERTY_ASSERTION_TAG: u16 = 113;
const NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG: u16 = 114;
const NEGATIVE_DATA_PROPERTY_ASSERTION_TAG: u16 = 116;
const SWRL_RULE_TAG: u16 = 148;
const TOP_DATA_PROPERTY_IRI: &[u8] = b"http://www.w3.org/2002/07/owl#topDataProperty";
const DATA_RANGE_ARITY_RULE: &str = "OWL2_DATA_RANGE_ARITY";
const DATA_RANGE_ARITY_MESSAGE: &str =
    "OWL 2 defines only unary data ranges, so the restriction must use exactly one data property";
const TOP_DATA_PROPERTY_RULE: &str = "OWL2DL_TOP_DATA_PROPERTY_POSITION";
const TOP_DATA_PROPERTY_MESSAGE: &str =
    "owl:topDataProperty may occur only as the super-property of a data subproperty axiom";
const ANONYMOUS_AXIOM_POSITION_RULE: &str = "OWL2DL_ANONYMOUS_AXIOM_POSITION";
const ANONYMOUS_AXIOM_POSITION_MESSAGE: &str =
    "anonymous individuals are forbidden in this axiom type";
const ANONYMOUS_CLASS_EXPRESSION_RULE: &str = "OWL2DL_ANONYMOUS_CLASS_EXPRESSION";
const ANONYMOUS_CLASS_EXPRESSION_MESSAGE: &str =
    "anonymous individuals are forbidden in ObjectOneOf and ObjectHasValue expressions";
const ANONYMOUS_GRAPH_CYCLE_RULE: &str = "OWL2DL_ANONYMOUS_GRAPH_CYCLE";
const ANONYMOUS_GRAPH_CYCLE_MESSAGE: &str =
    "the anonymous-individual object-assertion graph must be a forest";
const ANONYMOUS_PARALLEL_EDGE_RULE: &str = "OWL2DL_ANONYMOUS_PARALLEL_EDGE";
const ANONYMOUS_PARALLEL_EDGE_MESSAGE: &str =
    "at most one object-property assertion may connect an anonymous pair";
const ANONYMOUS_TREE_ROOT_RULE: &str = "OWL2DL_ANONYMOUS_TREE_ROOT";
const ANONYMOUS_TREE_ROOT_MESSAGE: &str =
    "each anonymous-individual tree must contain a vertex connected by at most one assertion to named individuals";
const PROPERTY_PUNNING_RULE: &str = "OWL2DL_PROPERTY_PUNNING";
const CLASS_DATATYPE_PUNNING_RULE: &str = "OWL2DL_CLASS_DATATYPE_PUNNING";
const RESERVED_VOCABULARY_RULE: &str = "OWL2DL_RESERVED_VOCABULARY";
const BUILTIN_ENTITY_KIND_RULE: &str = "OWL2DL_BUILTIN_ENTITY_KIND";
const MISSING_DECLARATION_RULE: &str = "OWL2DL_MISSING_DECLARATION";
const EXTENSION_COMPONENT_RULE: &str = "OWL2DL_EXTENSION_COMPONENT";
const EXTENSION_COMPONENT_MESSAGE: &str =
    "extension components such as SWRL are outside the OWL 2 DL reasoner scope";
const PROFILE_MANIFEST_BASE_BOUND: usize = 256;
const PROFILE_MANIFEST_ISSUE_BOUND: usize = 640;
const RESERVED_PREFIXES: &[&[u8]] = &[
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    b"http://www.w3.org/2000/01/rdf-schema#",
    b"http://www.w3.org/2001/XMLSchema#",
    b"http://www.w3.org/2002/07/owl#",
];
const BUILTIN_CLASSES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#Thing",
    b"http://www.w3.org/2002/07/owl#Nothing",
];
const BUILTIN_OBJECT_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#topObjectProperty",
    b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
];
const BUILTIN_DATA_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#topDataProperty",
    b"http://www.w3.org/2002/07/owl#bottomDataProperty",
];
const BUILTIN_ANNOTATION_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2000/01/rdf-schema#label",
    b"http://www.w3.org/2000/01/rdf-schema#comment",
    b"http://www.w3.org/2000/01/rdf-schema#seeAlso",
    b"http://www.w3.org/2000/01/rdf-schema#isDefinedBy",
    b"http://www.w3.org/2002/07/owl#deprecated",
    b"http://www.w3.org/2002/07/owl#versionInfo",
    b"http://www.w3.org/2002/07/owl#priorVersion",
    b"http://www.w3.org/2002/07/owl#backwardCompatibleWith",
    b"http://www.w3.org/2002/07/owl#incompatibleWith",
];
const BUILTIN_DATATYPES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#real",
    b"http://www.w3.org/2002/07/owl#rational",
    b"http://www.w3.org/2001/XMLSchema#decimal",
    b"http://www.w3.org/2001/XMLSchema#integer",
    b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger",
    b"http://www.w3.org/2001/XMLSchema#positiveInteger",
    b"http://www.w3.org/2001/XMLSchema#nonPositiveInteger",
    b"http://www.w3.org/2001/XMLSchema#negativeInteger",
    b"http://www.w3.org/2001/XMLSchema#long",
    b"http://www.w3.org/2001/XMLSchema#int",
    b"http://www.w3.org/2001/XMLSchema#short",
    b"http://www.w3.org/2001/XMLSchema#byte",
    b"http://www.w3.org/2001/XMLSchema#unsignedLong",
    b"http://www.w3.org/2001/XMLSchema#unsignedInt",
    b"http://www.w3.org/2001/XMLSchema#unsignedShort",
    b"http://www.w3.org/2001/XMLSchema#unsignedByte",
    b"http://www.w3.org/2001/XMLSchema#boolean",
    b"http://www.w3.org/2001/XMLSchema#float",
    b"http://www.w3.org/2001/XMLSchema#double",
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
    b"http://www.w3.org/2001/XMLSchema#string",
    b"http://www.w3.org/2001/XMLSchema#normalizedString",
    b"http://www.w3.org/2001/XMLSchema#token",
    b"http://www.w3.org/2001/XMLSchema#language",
    b"http://www.w3.org/2001/XMLSchema#Name",
    b"http://www.w3.org/2001/XMLSchema#NCName",
    b"http://www.w3.org/2001/XMLSchema#NMTOKEN",
    b"http://www.w3.org/2001/XMLSchema#hexBinary",
    b"http://www.w3.org/2001/XMLSchema#base64Binary",
    b"http://www.w3.org/2001/XMLSchema#anyURI",
    b"http://www.w3.org/2001/XMLSchema#dateTime",
    b"http://www.w3.org/2001/XMLSchema#dateTimeStamp",
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral",
    b"http://www.w3.org/2000/01/rdf-schema#Literal",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProfilePhaseLimits {
    pub max_slices: usize,
    pub max_axioms: usize,
    pub max_extensions: usize,
    pub max_issues: usize,
    pub max_anonymous_vertices: usize,
    pub max_anonymous_assertions: usize,
    pub max_entity_uses: usize,
    pub max_entity_declarations: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
    pub max_canonical_depth: usize,
    pub max_scope_maps: usize,
}

impl Default for ProfilePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_axioms: 10_000_000,
            max_extensions: 10_000_000,
            max_issues: 10_000_000,
            max_anonymous_vertices: 10_000_000,
            max_anonymous_assertions: 10_000_000,
            max_entity_uses: 10_000_000,
            max_entity_declarations: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
            max_canonical_depth: 512,
            max_scope_maps: 32,
        }
    }
}

/// Exact scalar-compatible issue fields available in structural-columns v1.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProfileIssue {
    pub rule_id: &'static str,
    pub severity: &'static str,
    pub message: Cow<'static, str>,
    pub constructor: Option<&'static str>,
    pub provenance_sha256: Option<[u8; 32]>,
}

type AnonymousKey = [u8; 64];

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AnonymousAssertion {
    axiom_key: Vec<u8>,
    provenance_sha256: [u8; 32],
    source: Option<AnonymousKey>,
    target: Option<AnonymousKey>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ProfileEntityKind {
    AnnotationProperty,
    Class,
    DataProperty,
    Datatype,
    NamedIndividual,
    ObjectProperty,
}

impl ProfileEntityKind {
    fn from_scalar<B: ByteSource>(value: ScalarRef<B>) -> EncodedResult<Self> {
        if value.kind() != ComponentKind::Enum {
            return Err(EncodedValidationError::invariant(
                "validated profile entity kind is not an enum",
            ));
        }
        if value.bytes_equal(b"annotation_property") {
            Ok(Self::AnnotationProperty)
        } else if value.bytes_equal(b"class") {
            Ok(Self::Class)
        } else if value.bytes_equal(b"data_property") {
            Ok(Self::DataProperty)
        } else if value.bytes_equal(b"datatype") {
            Ok(Self::Datatype)
        } else if value.bytes_equal(b"named_individual") {
            Ok(Self::NamedIndividual)
        } else if value.bytes_equal(b"object_property") {
            Ok(Self::ObjectProperty)
        } else {
            Err(EncodedValidationError::invariant(
                "validated profile entity kind is no longer recognized",
            ))
        }
    }

    const fn as_str(self) -> &'static str {
        match self {
            Self::AnnotationProperty => "annotation_property",
            Self::Class => "class",
            Self::DataProperty => "data_property",
            Self::Datatype => "datatype",
            Self::NamedIndividual => "named_individual",
            Self::ObjectProperty => "object_property",
        }
    }

    const fn is_property(self) -> bool {
        matches!(
            self,
            Self::AnnotationProperty | Self::DataProperty | Self::ObjectProperty
        )
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileEntityIdentity {
    iri: Vec<u8>,
    kind: ProfileEntityKind,
}

/// Transactional profile result. Violations never use the error channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProfilePhase {
    pub issues: Vec<ProfileIssue>,
    pub conforms: bool,
    pub axioms_checked: usize,
    pub extensions_checked: usize,
    pub work: u64,
    pub owned_bytes: usize,
    axiom_keys: Vec<Vec<u8>>,
    extension_keys: Vec<Vec<u8>>,
    anonymous_vertices: Vec<AnonymousKey>,
    anonymous_assertions: Vec<AnonymousAssertion>,
    entity_uses: Vec<ProfileEntityIdentity>,
    entity_declarations: Vec<ProfileEntityIdentity>,
    manifest_limit: usize,
}

impl ProfilePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase(self)?;
        let issue_bound = self.issues.iter().try_fold(0_usize, |total, issue| {
            issue
                .message
                .len()
                .checked_mul(6)
                .and_then(|message| message.checked_add(PROFILE_MANIFEST_ISSUE_BOUND))
                .and_then(|issue| total.checked_add(issue))
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile manifest size bound overflowed")
                })
        })?;
        let manifest_bound = issue_bound
            .checked_add(PROFILE_MANIFEST_BASE_BOUND)
            .ok_or_else(|| {
                EncodedValidationError::resource("profile manifest size bound overflowed")
            })?;
        if manifest_bound > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "profile manifest exceeds its byte limit",
            ));
        }
        let mut ordered_rule_ids = Vec::new();
        reserve_exact(
            &mut ordered_rule_ids,
            self.issues.len(),
            "profile rule-ID manifest allocation failed",
        )?;
        ordered_rule_ids.extend(self.issues.iter().map(|issue| issue.rule_id));

        let mut issues = Vec::new();
        reserve_exact(
            &mut issues,
            self.issues.len(),
            "profile issue manifest allocation failed",
        )?;
        issues.extend(self.issues.iter().map(|issue| {
            ProfileIssueManifest {
                rule_id: issue.rule_id,
                severity: issue.severity,
                message: issue.message.as_ref(),
                constructor: issue.constructor,
                provenance_sha256: issue
                    .provenance_sha256
                    .map(|value| crate::model::hex(&value)),
            }
        }));
        let encoded = serde_json::to_vec(&ProfileManifest {
            schema_version: PROFILE_PHASE_SCHEMA_VERSION,
            family: "owl2_dl_profile",
            conforms: self.conforms,
            axioms_checked: self.axioms_checked,
            extensions_checked: self.extensions_checked,
            ordered_rule_ids,
            issues,
        })
        .map_err(|_| EncodedValidationError::invariant("profile manifest serialization failed"))?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "profile manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct ProfileManifest<'a> {
    schema_version: u16,
    family: &'static str,
    conforms: bool,
    axioms_checked: usize,
    extensions_checked: usize,
    ordered_rule_ids: Vec<&'a str>,
    issues: Vec<ProfileIssueManifest<'a>>,
}

#[derive(Serialize)]
struct ProfileIssueManifest<'a> {
    rule_id: &'a str,
    severity: &'a str,
    message: &'a str,
    constructor: Option<&'a str>,
    provenance_sha256: Option<String>,
}

/// Separates encoded operational failures from caller-owned cancellation.
#[derive(Debug, Eq, PartialEq)]
pub enum ProfilePhaseError<E> {
    Encoded(EncodedValidationError),
    Control(E),
}

impl<E> From<EncodedValidationError> for ProfilePhaseError<E> {
    fn from(error: EncodedValidationError) -> Self {
        Self::Encoded(error)
    }
}

type ControlledResult<T, E> = Result<T, ProfilePhaseError<E>>;

struct PhaseBudget {
    limits: ProfilePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: ProfilePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("profile work exceeds u64"))?;
        self.claim_work_u64(amount)
    }

    fn claim_work_u64(&mut self, amount: u64) -> EncodedResult<()> {
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("profile work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "profile compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("profile owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "profile compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn claim_axiom(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_axioms {
            Err(EncodedValidationError::resource(
                "profile axiom count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_extension(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_extensions {
            Err(EncodedValidationError::resource(
                "profile extension count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_issue(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_issues {
            Err(EncodedValidationError::resource(
                "profile issue count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_anonymous_vertex(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_anonymous_vertices {
            Err(EncodedValidationError::resource(
                "profile anonymous vertex count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_anonymous_assertion(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_anonymous_assertions {
            Err(EncodedValidationError::resource(
                "profile anonymous assertion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_entity_use(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_entity_uses {
            Err(EncodedValidationError::resource(
                "profile entity use count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_entity_declaration(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_entity_declarations {
            Err(EncodedValidationError::resource(
                "profile entity declaration count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }
}

impl CanonicalBudget for PhaseBudget {
    fn canonical_max_depth(&self) -> usize {
        self.limits.max_canonical_depth
    }

    fn canonical_max_scope_maps(&self) -> usize {
        self.limits.max_scope_maps
    }

    fn claim_canonical_work(&mut self, amount: usize) -> EncodedResult<()> {
        self.claim_work(amount)
    }

    fn claim_canonical_owned(&mut self, amount: usize) -> EncodedResult<()> {
        self.claim_owned(amount)
    }
}

#[derive(Clone, Copy)]
struct RootPostings<S: ByteSource> {
    postings: S,
    count: usize,
    cursor: usize,
}

impl<S: ByteSource> RootPostings<S> {
    fn new(postings: S, root_count: usize, name: &'static str) -> EncodedResult<Self> {
        if postings.len() % 4 != 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded profile root {name} contain a partial u32"
            )));
        }
        let count = postings.len() / 4;
        if count == 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded profile root {name} are empty"
            )));
        }
        let mut previous = 0_usize;
        for index in 0..count {
            let current = usize::try_from(u32_at(postings, index, name)?).map_err(|_| {
                EncodedValidationError::resource(format!(
                    "encoded profile root {name} exceeds the platform index width"
                ))
            })?;
            if current <= previous || current > root_count {
                return Err(EncodedValidationError::protocol(format!(
                    "encoded profile root {name} are not sorted unique in-range IDs"
                )));
            }
            previous = current;
        }
        Ok(Self {
            postings,
            count,
            cursor: 0,
        })
    }

    fn contains(&mut self, root_index: usize) -> EncodedResult<bool> {
        if self.cursor >= self.count {
            return Ok(false);
        }
        let current = usize::try_from(u32_at(self.postings, self.cursor, "profile root posting")?)
            .map_err(|_| {
                EncodedValidationError::resource(
                    "encoded profile root posting exceeds the platform index width",
                )
            })?;
        let local_root_id = root_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("encoded profile root index overflowed")
        })?;
        if current == local_root_id {
            self.cursor += 1;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[derive(Clone, Copy)]
enum RootSelection<S: ByteSource> {
    All,
    Include(RootPostings<S>),
    Exclude(RootPostings<S>),
}

impl<S: ByteSource> RootSelection<S> {
    const fn selected_count(&self, root_count: usize) -> usize {
        match self {
            Self::All => root_count,
            Self::Include(postings) => postings.count,
            Self::Exclude(postings) => root_count - postings.count,
        }
    }

    const fn validation_work(&self) -> usize {
        match self {
            Self::All => 0,
            Self::Include(postings) | Self::Exclude(postings) => postings.count,
        }
    }

    fn excludes(&mut self, root_index: usize) -> EncodedResult<bool> {
        match self {
            Self::All => Ok(false),
            Self::Include(postings) => Ok(!postings.contains(root_index)?),
            Self::Exclude(postings) => postings.contains(root_index),
        }
    }
}

/// Compile all roots with a no-op control.
pub fn compile_profile_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
) -> EncodedResult<ProfilePhase> {
    let mut control = |_phase| Ok::<(), Infallible>(());
    into_encoded(compile_profile_phase_controlled(
        model,
        scope_maps,
        limits,
        &mut control,
    ))
}

/// Compile all roots while polling caller-owned cancellation within the phase.
pub fn compile_profile_phase_controlled<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    compile_profile_phase_with_selection(
        model,
        scope_maps,
        limits,
        RootSelection::<&[u8]>::All,
        control,
    )
}

/// Compile a source-local ALL, INCLUDE, or EXCLUDE selection.
pub fn compile_profile_phase_selected_controlled<B: ByteSource, S: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    posting_mode: u8,
    postings: S,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    let selection = match posting_mode {
        POSTINGS_ALL if postings.is_empty() => RootSelection::All,
        POSTINGS_ALL => {
            return Err(EncodedValidationError::protocol(
                "ALL encoded profile root selection carries postings",
            )
            .into());
        }
        POSTINGS_INCLUDE => RootSelection::Include(
            RootPostings::new(postings, model.summary().root_count, "inclusions")
                .map_err(ProfilePhaseError::Encoded)?,
        ),
        POSTINGS_EXCLUDE => RootSelection::Exclude(
            RootPostings::new(postings, model.summary().root_count, "exclusions")
                .map_err(ProfilePhaseError::Encoded)?,
        ),
        _ => {
            return Err(EncodedValidationError::protocol(
                "encoded profile root selection mode is unsupported",
            )
            .into());
        }
    };
    compile_profile_phase_with_selection(model, scope_maps, limits, selection, control)
}

fn compile_profile_phase_with_selection<B: ByteSource, S: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    mut selection: RootSelection<S>,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    poll(control, "profile-preflight")?;
    let summary = model.summary();
    let mut budget = PhaseBudget::new(limits);
    canonical::validate_scope_maps(scope_maps, &mut budget).map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_work(selection.validation_work())
        .map_err(ProfilePhaseError::Encoded)?;

    let node_count = summary.node_count;
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(node_count.checked_mul(size_of::<NodeId>()).ok_or_else(|| {
            EncodedValidationError::resource("profile traversal stack size overflowed")
        })?)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut marks = Vec::new();
    reserve_exact(
        &mut marks,
        node_count,
        "profile traversal mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    marks.resize(node_count, 0_u32);
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_seen = Vec::new();
    reserve_exact(
        &mut anonymous_seen,
        node_count,
        "profile anonymous-node mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    anonymous_seen.resize(node_count, 0_u8);
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_seen = Vec::new();
    reserve_exact(
        &mut entity_seen,
        node_count,
        "profile entity-node mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    entity_seen.resize(node_count, 0_u8);
    let mut stack = Vec::new();
    reserve_exact(
        &mut stack,
        node_count,
        "profile traversal stack allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;

    let selected_count = selection.selected_count(summary.root_count);
    budget
        .claim_owned(
            selected_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "profile canonical axiom vector size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut axiom_keys = Vec::new();
    reserve_exact(
        &mut axiom_keys,
        selected_count,
        "profile canonical axiom allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut extension_keys = Vec::new();
    let mut issues = Vec::new();
    let mut anonymous_vertices = Vec::new();
    let mut anonymous_assertions = Vec::new();
    let mut entity_uses = Vec::new();
    let mut entity_declarations = Vec::new();
    let mut epoch = 0_u32;

    for root_index in 0..summary.root_count {
        poll(control, "profile-root")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        if selection
            .excludes(root_index)
            .map_err(ProfilePhaseError::Encoded)?
        {
            continue;
        }
        let root = model
            .root(root_index)
            .map_err(ProfilePhaseError::Encoded)?
            .ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "validated profile root row disappeared",
                ))
            })?;
        match root.kind() {
            RootKind::OntologyAnnotation => {
                epoch = epoch.checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile traversal epoch overflowed",
                    ))
                })?;
                enqueue_node(root.node(), &mut marks, epoch, &mut stack)
                    .map_err(ProfilePhaseError::Encoded)?;
                while let Some(identifier) = stack.pop() {
                    poll(control, "profile-node")?;
                    budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                    let node = model.node(identifier).map_err(ProfilePhaseError::Encoded)?;
                    if node.tag() == ENTITY_TAG {
                        retain_entity_use(
                            model,
                            identifier,
                            &mut entity_seen,
                            &mut entity_uses,
                            &mut budget,
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                    }
                    for field_index in node.fields() {
                        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                        let component = required_component(
                            model
                                .field(field_index)
                                .map_err(ProfilePhaseError::Encoded)?,
                            "profile ontology annotation field",
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                        enqueue_component(
                            model,
                            component,
                            &mut marks,
                            epoch,
                            &mut stack,
                            &mut budget,
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                    }
                }
                continue;
            }
            RootKind::Axiom => {}
            RootKind::Extension => {
                budget
                    .claim_extension(extension_keys.len().checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource("profile extension count overflowed")
                    })?)
                    .map_err(ProfilePhaseError::Encoded)?;
                let node = model
                    .node(root.node())
                    .map_err(ProfilePhaseError::Encoded)?;
                if node.tag() != SWRL_RULE_TAG {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile extension root is not a SWRL rule",
                        ),
                    ));
                }
                poll(control, "profile-extension-provenance")?;
                let key =
                    canonical::canonical_node_key(model, root.node(), scope_maps, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_work(key.len())
                    .map_err(ProfilePhaseError::Encoded)?;
                let provenance_sha256: [u8; 32] = Sha256::digest(&key).into();
                budget
                    .claim_owned(size_of::<Vec<u8>>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(
                    &mut extension_keys,
                    "profile canonical extension allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                extension_keys.push(key);

                let following = issues.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile issue count overflowed",
                    ))
                })?;
                budget
                    .claim_issue(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_owned(size_of::<ProfileIssue>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(&mut issues, "profile issue allocation failed")
                    .map_err(ProfilePhaseError::Encoded)?;
                issues.push(ProfileIssue {
                    rule_id: EXTENSION_COMPONENT_RULE,
                    severity: "error",
                    message: Cow::Borrowed(EXTENSION_COMPONENT_MESSAGE),
                    constructor: Some("SWRLRule"),
                    provenance_sha256: Some(provenance_sha256),
                });
                continue;
            }
        }
        budget
            .claim_axiom(axiom_keys.len().checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("profile axiom count overflowed")
            })?)
            .map_err(ProfilePhaseError::Encoded)?;
        let axiom_tag = model
            .node(root.node())
            .map_err(ProfilePhaseError::Encoded)?
            .tag();
        let axiom_constructor = RootHandler::from_root(RootKind::Axiom, axiom_tag)
            .map_err(ProfilePhaseError::Encoded)?
            .as_str();
        if axiom_tag == DECLARATION_TAG {
            let identity = declaration_entity(model, root.node(), &mut budget)
                .map_err(ProfilePhaseError::Encoded)?;
            retain_entity_declaration(identity, &mut entity_declarations, &mut budget)
                .map_err(ProfilePhaseError::Encoded)?;
        }
        let anonymous_axiom_forbidden = matches!(
            axiom_tag,
            SAME_INDIVIDUAL_TAG
                | DIFFERENT_INDIVIDUALS_TAG
                | NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG
                | NEGATIVE_DATA_PROPERTY_ASSERTION_TAG
        );
        let top_data_property_allowed = allows_top_data_property(model, root.node(), &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;

        poll(control, "profile-provenance")?;
        let key = canonical::canonical_node_key(model, root.node(), scope_maps, &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work(key.len())
            .map_err(ProfilePhaseError::Encoded)?;
        let provenance_sha256: [u8; 32] = Sha256::digest(&key).into();
        if axiom_tag == OBJECT_PROPERTY_ASSERTION_TAG {
            let (source, target) =
                anonymous_assertion_endpoints(model, root.node(), scope_maps, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?;
            if source.is_some() || target.is_some() {
                let following = anonymous_assertions.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile anonymous assertion count overflowed",
                    ))
                })?;
                budget
                    .claim_anonymous_assertion(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                let axiom_key = clone_profile_bytes(
                    &key,
                    &mut budget,
                    "profile anonymous assertion key allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                reserve_profile_one(
                    &mut anonymous_assertions,
                    &mut budget,
                    "profile anonymous assertion allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                anonymous_assertions.push(AnonymousAssertion {
                    axiom_key,
                    provenance_sha256,
                    source,
                    target,
                });
            }
        }
        axiom_keys.push(key);

        epoch = epoch.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile traversal epoch overflowed",
            ))
        })?;
        enqueue_node(root.node(), &mut marks, epoch, &mut stack)
            .map_err(ProfilePhaseError::Encoded)?;
        let mut top_data_property_occurs = false;
        let mut anonymous_individual_occurs = false;
        while let Some(identifier) = stack.pop() {
            poll(control, "profile-node")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            let node = model.node(identifier).map_err(ProfilePhaseError::Encoded)?;
            if node.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                anonymous_individual_occurs = true;
                let anonymous_index = usize::try_from(identifier.get() - 1).map_err(|_| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile anonymous node index exceeds the platform width",
                    ))
                })?;
                let seen = anonymous_seen.get_mut(anonymous_index).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile anonymous node identifier is out of range",
                    ))
                })?;
                if *seen == 0 {
                    let following = anonymous_vertices.len().checked_add(1).ok_or_else(|| {
                        ProfilePhaseError::Encoded(EncodedValidationError::resource(
                            "profile anonymous vertex count overflowed",
                        ))
                    })?;
                    budget
                        .claim_anonymous_vertex(following)
                        .map_err(ProfilePhaseError::Encoded)?;
                    let key = anonymous_key(model, identifier, scope_maps, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?;
                    reserve_profile_one(
                        &mut anonymous_vertices,
                        &mut budget,
                        "profile anonymous vertex allocation failed",
                    )
                    .map_err(ProfilePhaseError::Encoded)?;
                    anonymous_vertices.push(key);
                    *seen = 1;
                }
            }
            if node.tag() == ENTITY_TAG {
                retain_entity_use(
                    model,
                    identifier,
                    &mut entity_seen,
                    &mut entity_uses,
                    &mut budget,
                )
                .map_err(ProfilePhaseError::Encoded)?;
            }
            let anonymous_expression =
                if matches!(node.tag(), OBJECT_ONE_OF_TAG | OBJECT_HAS_VALUE_TAG) {
                    forbidden_anonymous_expression(model, identifier, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?
                } else {
                    None
                };
            if let Some(constructor) = anonymous_expression {
                let following = issues.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile issue count overflowed",
                    ))
                })?;
                budget
                    .claim_issue(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_owned(size_of::<ProfileIssue>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(&mut issues, "profile issue allocation failed")
                    .map_err(ProfilePhaseError::Encoded)?;
                issues.push(ProfileIssue {
                    rule_id: ANONYMOUS_CLASS_EXPRESSION_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_CLASS_EXPRESSION_MESSAGE),
                    constructor: Some(constructor),
                    provenance_sha256: Some(provenance_sha256),
                });
            }
            if node.tag() == ENTITY_TAG
                && is_top_data_property(model, identifier, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?
            {
                top_data_property_occurs = true;
            }
            if matches!(
                node.tag(),
                DATA_SOME_VALUES_FROM_TAG | DATA_ALL_VALUES_FROM_TAG
            ) {
                let property_field = required_component(
                    model
                        .field(node.fields().start)
                        .map_err(ProfilePhaseError::Encoded)?,
                    "profile data restriction property sequence",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                let ComponentValue::Collection(properties) = model
                    .resolve(property_field)
                    .map_err(ProfilePhaseError::Encoded)?
                else {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile data restriction properties are not a sequence",
                        ),
                    ));
                };
                if properties.kind() != ComponentKind::Sequence {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile data restriction properties lost sequence order",
                        ),
                    ));
                }
                if properties.len() != 1 {
                    let following = issues.len().checked_add(1).ok_or_else(|| {
                        ProfilePhaseError::Encoded(EncodedValidationError::resource(
                            "profile issue count overflowed",
                        ))
                    })?;
                    budget
                        .claim_issue(following)
                        .map_err(ProfilePhaseError::Encoded)?;
                    budget
                        .claim_owned(size_of::<ProfileIssue>())
                        .map_err(ProfilePhaseError::Encoded)?;
                    reserve_one(&mut issues, "profile issue allocation failed")
                        .map_err(ProfilePhaseError::Encoded)?;
                    issues.push(ProfileIssue {
                        rule_id: DATA_RANGE_ARITY_RULE,
                        severity: "error",
                        message: Cow::Borrowed(DATA_RANGE_ARITY_MESSAGE),
                        constructor: Some(if node.tag() == DATA_SOME_VALUES_FROM_TAG {
                            "DataSomeValuesFrom"
                        } else {
                            "DataAllValuesFrom"
                        }),
                        provenance_sha256: Some(provenance_sha256),
                    });
                }
            }
            for field_index in node.fields() {
                budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                let component = required_component(
                    model
                        .field(field_index)
                        .map_err(ProfilePhaseError::Encoded)?,
                    "profile node field",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                enqueue_component(model, component, &mut marks, epoch, &mut stack, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?;
            }
        }
        if anonymous_individual_occurs && anonymous_axiom_forbidden {
            let following = issues.len().checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile issue count overflowed",
                ))
            })?;
            budget
                .claim_issue(following)
                .map_err(ProfilePhaseError::Encoded)?;
            budget
                .claim_owned(size_of::<ProfileIssue>())
                .map_err(ProfilePhaseError::Encoded)?;
            reserve_one(&mut issues, "profile issue allocation failed")
                .map_err(ProfilePhaseError::Encoded)?;
            issues.push(ProfileIssue {
                rule_id: ANONYMOUS_AXIOM_POSITION_RULE,
                severity: "error",
                message: Cow::Borrowed(ANONYMOUS_AXIOM_POSITION_MESSAGE),
                constructor: Some(axiom_constructor),
                provenance_sha256: Some(provenance_sha256),
            });
        }
        if top_data_property_occurs && !top_data_property_allowed {
            let following = issues.len().checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile issue count overflowed",
                ))
            })?;
            budget
                .claim_issue(following)
                .map_err(ProfilePhaseError::Encoded)?;
            budget
                .claim_owned(size_of::<ProfileIssue>())
                .map_err(ProfilePhaseError::Encoded)?;
            reserve_one(&mut issues, "profile issue allocation failed")
                .map_err(ProfilePhaseError::Encoded)?;
            issues.push(ProfileIssue {
                rule_id: TOP_DATA_PROPERTY_RULE,
                severity: "error",
                message: Cow::Borrowed(TOP_DATA_PROPERTY_MESSAGE),
                constructor: Some(axiom_constructor),
                provenance_sha256: Some(provenance_sha256),
            });
        }
    }

    poll(control, "profile-canonicalize")?;
    budget
        .claim_work(sort_work(anonymous_vertices.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_vertices.sort_unstable();
    anonymous_vertices.dedup();
    budget
        .claim_work(sort_work(anonymous_assertions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_assertions.sort();
    anonymous_assertions.dedup();
    append_anonymous_graph_issues(
        &anonymous_vertices,
        &anonymous_assertions,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(entity_uses.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_uses.sort();
    entity_uses.dedup();
    budget
        .claim_work(sort_work(entity_declarations.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_declarations.sort();
    entity_declarations.dedup();
    append_entity_issues(
        &entity_uses,
        &entity_declarations,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    issues.sort();
    issues.dedup();
    budget
        .claim_work(sort_work(axiom_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    axiom_keys.sort();
    axiom_keys.dedup();
    budget
        .claim_work(sort_work(extension_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    extension_keys.sort();
    extension_keys.dedup();
    let phase = ProfilePhase {
        conforms: issues.is_empty(),
        axioms_checked: axiom_keys.len(),
        extensions_checked: extension_keys.len(),
        issues,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        axiom_keys,
        extension_keys,
        anonymous_vertices,
        anonymous_assertions,
        entity_uses,
        entity_declarations,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-complete")?;
    Ok(phase)
}

/// Canonically merge source-local reports without losing selection semantics.
pub fn merge_profile_phases(
    phases: Vec<ProfilePhase>,
    limits: ProfilePhaseLimits,
) -> EncodedResult<ProfilePhase> {
    let mut control = |_phase| Ok::<(), Infallible>(());
    into_encoded(merge_profile_phases_controlled(
        phases,
        limits,
        &mut control,
    ))
}

pub fn merge_profile_phases_controlled<E>(
    phases: Vec<ProfilePhase>,
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    if phases.is_empty() {
        return Err(EncodedValidationError::invariant(
            "profile merge requires at least one source phase",
        )
        .into());
    }
    if phases.len() > limits.max_slices {
        return Err(
            EncodedValidationError::resource("profile merge exceeds its slice limit").into(),
        );
    }
    poll(control, "profile-merge-preflight")?;
    let issue_count = phases.iter().try_fold(0_usize, |total, phase| {
        let local = phase
            .issues
            .iter()
            .filter(|issue| !is_recomputed_profile_rule(issue.rule_id))
            .count();
        total.checked_add(local).ok_or_else(|| {
            EncodedValidationError::resource("merged profile issue count overflowed")
        })
    })?;
    let axiom_count = phases.iter().try_fold(0_usize, |total, phase| {
        total.checked_add(phase.axiom_keys.len()).ok_or_else(|| {
            EncodedValidationError::resource("merged profile axiom count overflowed")
        })
    })?;
    let extension_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.extension_keys.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile extension count overflowed")
            })
    })?;
    let anonymous_vertex_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.anonymous_vertices.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile anonymous vertex count overflowed")
            })
    })?;
    let anonymous_assertion_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.anonymous_assertions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile anonymous assertion count overflowed",
                )
            })
    })?;
    let entity_use_count = phases.iter().try_fold(0_usize, |total, phase| {
        total.checked_add(phase.entity_uses.len()).ok_or_else(|| {
            EncodedValidationError::resource("merged profile entity use count overflowed")
        })
    })?;
    let entity_declaration_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.entity_declarations.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile entity declaration count overflowed",
                )
            })
    })?;
    if issue_count > limits.max_issues {
        return Err(EncodedValidationError::resource(
            "merged profile issue count exceeds its limit",
        )
        .into());
    }
    if axiom_count > limits.max_axioms {
        return Err(EncodedValidationError::resource(
            "merged profile axiom count exceeds its limit",
        )
        .into());
    }
    if extension_count > limits.max_extensions {
        return Err(EncodedValidationError::resource(
            "merged profile extension count exceeds its limit",
        )
        .into());
    }
    if anonymous_vertex_count > limits.max_anonymous_vertices {
        return Err(EncodedValidationError::resource(
            "merged profile anonymous vertex count exceeds its limit",
        )
        .into());
    }
    if anonymous_assertion_count > limits.max_anonymous_assertions {
        return Err(EncodedValidationError::resource(
            "merged profile anonymous assertion count exceeds its limit",
        )
        .into());
    }
    if entity_use_count > limits.max_entity_uses {
        return Err(EncodedValidationError::resource(
            "merged profile entity use count exceeds its limit",
        )
        .into());
    }
    if entity_declaration_count > limits.max_entity_declarations {
        return Err(EncodedValidationError::resource(
            "merged profile entity declaration count exceeds its limit",
        )
        .into());
    }

    let mut budget = PhaseBudget::new(limits);
    let mut issues = Vec::new();
    reserve_exact(
        &mut issues,
        issue_count,
        "merged profile issue allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            issue_count
                .checked_mul(size_of::<ProfileIssue>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile issue size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut axiom_keys = Vec::new();
    reserve_exact(
        &mut axiom_keys,
        axiom_count,
        "merged profile axiom allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            axiom_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile axiom size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut extension_keys = Vec::new();
    reserve_exact(
        &mut extension_keys,
        extension_count,
        "merged profile extension allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            extension_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile extension size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_vertices = Vec::new();
    reserve_exact(
        &mut anonymous_vertices,
        anonymous_vertex_count,
        "merged profile anonymous vertex allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            anonymous_vertex_count
                .checked_mul(size_of::<AnonymousKey>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile anonymous vertex size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_assertions = Vec::new();
    reserve_exact(
        &mut anonymous_assertions,
        anonymous_assertion_count,
        "merged profile anonymous assertion allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            anonymous_assertion_count
                .checked_mul(size_of::<AnonymousAssertion>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile anonymous assertion size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_uses = Vec::new();
    reserve_exact(
        &mut entity_uses,
        entity_use_count,
        "merged profile entity use allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            entity_use_count
                .checked_mul(size_of::<ProfileEntityIdentity>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile entity use size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_declarations = Vec::new();
    reserve_exact(
        &mut entity_declarations,
        entity_declaration_count,
        "merged profile entity declaration allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            entity_declaration_count
                .checked_mul(size_of::<ProfileEntityIdentity>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile entity declaration size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;

    for mut phase in phases {
        validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work_u64(phase.work)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_owned(phase.owned_bytes)
            .map_err(ProfilePhaseError::Encoded)?;
        issues.extend(
            phase
                .issues
                .drain(..)
                .filter(|issue| !is_recomputed_profile_rule(issue.rule_id)),
        );
        axiom_keys.append(&mut phase.axiom_keys);
        extension_keys.append(&mut phase.extension_keys);
        anonymous_vertices.append(&mut phase.anonymous_vertices);
        anonymous_assertions.append(&mut phase.anonymous_assertions);
        entity_uses.append(&mut phase.entity_uses);
        entity_declarations.append(&mut phase.entity_declarations);
        poll(control, "profile-merge-source")?;
    }
    budget
        .claim_work(sort_work(anonymous_vertices.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_vertices.sort_unstable();
    anonymous_vertices.dedup();
    budget
        .claim_work(sort_work(anonymous_assertions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_assertions.sort();
    anonymous_assertions.dedup();
    append_anonymous_graph_issues(
        &anonymous_vertices,
        &anonymous_assertions,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(entity_uses.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_uses.sort();
    entity_uses.dedup();
    budget
        .claim_work(sort_work(entity_declarations.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_declarations.sort();
    entity_declarations.dedup();
    append_entity_issues(
        &entity_uses,
        &entity_declarations,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    issues.sort();
    issues.dedup();
    budget
        .claim_work(sort_work(axiom_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    axiom_keys.sort();
    axiom_keys.dedup();
    budget
        .claim_work(sort_work(extension_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    extension_keys.sort();
    extension_keys.dedup();
    let phase = ProfilePhase {
        conforms: issues.is_empty(),
        axioms_checked: axiom_keys.len(),
        extensions_checked: extension_keys.len(),
        issues,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        axiom_keys,
        extension_keys,
        anonymous_vertices,
        anonymous_assertions,
        entity_uses,
        entity_declarations,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-merge-complete")?;
    Ok(phase)
}

fn declaration_entity<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileEntityIdentity> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != DECLARATION_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated declaration lost its schema-1 shape",
        ));
    }
    let entity = required_node(model, node.fields().start, "profile declared entity")?;
    profile_entity_identity(model, entity, budget)
}

fn retain_entity_use<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    seen: &mut [u8],
    uses: &mut Vec<ProfileEntityIdentity>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let index = usize::try_from(identifier.get() - 1).map_err(|_| {
        EncodedValidationError::invariant("profile entity node index exceeds the platform width")
    })?;
    let retained = seen.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("profile entity node identifier is out of range")
    })?;
    if *retained != 0 {
        return Ok(());
    }
    let following = uses
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity use count overflowed"))?;
    budget.claim_entity_use(following)?;
    let identity = profile_entity_identity(model, identifier, budget)?;
    reserve_profile_one(uses, budget, "profile entity use allocation failed")?;
    uses.push(identity);
    *retained = 1;
    Ok(())
}

fn retain_entity_declaration(
    identity: ProfileEntityIdentity,
    declarations: &mut Vec<ProfileEntityIdentity>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = declarations.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile entity declaration count overflowed")
    })?;
    budget.claim_entity_declaration(following)?;
    reserve_profile_one(
        declarations,
        budget,
        "profile entity declaration allocation failed",
    )?;
    declarations.push(identity);
    Ok(())
}

fn profile_entity_identity<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileEntityIdentity> {
    budget.claim_work(1)?;
    let entity = model.node(identifier)?;
    if entity.tag() != ENTITY_TAG || entity.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity lost its schema-1 shape",
        ));
    }
    let fields = entity.fields();
    let kind_component = required_component(model.field(fields.start)?, "profile entity kind")?;
    let ComponentValue::Scalar(kind_value) = model.resolve(kind_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not scalar",
        ));
    };
    budget.claim_work(kind_value.len())?;
    let kind = ProfileEntityKind::from_scalar(kind_value)?;
    let iri_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity field index overflowed"))?;
    let iri_identifier = required_node(model, iri_field, "profile entity IRI")?;
    let iri_node = model.node(iri_identifier)?;
    if iri_node.tag() != IRI_TAG || iri_node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI lost its schema-1 shape",
        ));
    }
    let iri_component = required_component(
        model.field(iri_node.fields().start)?,
        "profile entity IRI text",
    )?;
    let ComponentValue::Scalar(iri_value) = model.resolve(iri_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI text is not scalar",
        ));
    };
    if iri_value.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI is not text",
        ));
    }
    let iri = clone_profile_scalar(iri_value, budget, "profile entity IRI allocation failed")?;
    std::str::from_utf8(&iri).map_err(|_| {
        EncodedValidationError::invariant("validated profile entity IRI is no longer UTF-8")
    })?;
    Ok(ProfileEntityIdentity { iri, kind })
}

fn clone_profile_scalar<B: ByteSource>(
    value: ScalarRef<B>,
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<Vec<u8>> {
    budget.claim_work(value.len())?;
    budget.claim_owned(value.len())?;
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(message))?;
    for index in 0..value.len() {
        owned.push(value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("validated profile scalar disappeared")
        })?);
    }
    Ok(owned)
}

fn append_entity_issues<E>(
    uses: &[ProfileEntityIdentity],
    declarations: &[ProfileEntityIdentity],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if uses.is_empty() {
        return Ok(());
    }
    poll(control, "profile-entity-preflight")?;
    let mut start = 0_usize;
    while start < uses.len() {
        poll(control, "profile-entity-iri")?;
        let mut end = start + 1;
        while end < uses.len() && uses[end].iri == uses[start].iri {
            budget.claim_work(1)?;
            end += 1;
        }
        let group = &uses[start..end];
        let iri_bytes = &group[0].iri;
        let iri = std::str::from_utf8(iri_bytes).map_err(|_| {
            EncodedValidationError::invariant("validated profile entity IRI is no longer UTF-8")
        })?;
        let property_kinds = group
            .iter()
            .filter(|identity| identity.kind.is_property())
            .count();
        budget.claim_work(group.len())?;
        if property_kinds > 1 {
            push_dynamic_profile_issue(
                issues,
                PROPERTY_PUNNING_RULE,
                &["IRI is used for more than one property kind: ", iri],
                budget,
            )?;
        }
        budget.claim_work(group.len().saturating_mul(2))?;
        if group
            .iter()
            .any(|identity| identity.kind == ProfileEntityKind::Class)
            && group
                .iter()
                .any(|identity| identity.kind == ProfileEntityKind::Datatype)
        {
            push_dynamic_profile_issue(
                issues,
                CLASS_DATATYPE_PUNNING_RULE,
                &["IRI is used as both class and datatype: ", iri],
                budget,
            )?;
        }

        let reserved = reserved_iri(iri_bytes, budget)?;
        let builtin = if reserved {
            builtin_entity_kind(iri_bytes, budget)?
        } else {
            None
        };
        if reserved {
            if let Some(expected) = builtin {
                budget.claim_work(group.len())?;
                if group.iter().any(|identity| identity.kind != expected) {
                    push_dynamic_profile_issue(
                        issues,
                        BUILTIN_ENTITY_KIND_RULE,
                        &["built-in IRI is used with an illegal entity kind: ", iri],
                        budget,
                    )?;
                }
            } else {
                push_dynamic_profile_issue(
                    issues,
                    RESERVED_VOCABULARY_RULE,
                    &[
                        "reserved vocabulary IRI is not an OWL 2 built-in entity: ",
                        iri,
                    ],
                    budget,
                )?;
            }
        }

        if builtin.is_none() {
            for identity in group {
                budget.claim_work(search_work(declarations.len()))?;
                if identity.kind != ProfileEntityKind::NamedIndividual
                    && declarations.binary_search(identity).is_err()
                {
                    push_dynamic_profile_issue(
                        issues,
                        MISSING_DECLARATION_RULE,
                        &["used ", identity.kind.as_str(), " is not declared: ", iri],
                        budget,
                    )?;
                }
            }
        }
        start = end;
    }
    poll(control, "profile-entity-complete")?;
    Ok(())
}

fn push_dynamic_profile_issue(
    issues: &mut Vec<ProfileIssue>,
    rule_id: &'static str,
    message_parts: &[&str],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let length = message_parts.iter().try_fold(0_usize, |total, part| {
        total
            .checked_add(part.len())
            .ok_or_else(|| EncodedValidationError::resource("profile issue message overflowed"))
    })?;
    budget.claim_owned(length)?;
    let mut message = String::new();
    message
        .try_reserve_exact(length)
        .map_err(|_| EncodedValidationError::resource("profile issue message allocation failed"))?;
    for part in message_parts {
        message.push_str(part);
    }
    push_profile_issue(
        issues,
        ProfileIssue {
            rule_id,
            severity: "error",
            message: Cow::Owned(message),
            constructor: None,
            provenance_sha256: None,
        },
        budget,
    )
}

fn reserved_iri(iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<bool> {
    for prefix in RESERVED_PREFIXES {
        budget.claim_work(1)?;
        if iri.starts_with(prefix) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn builtin_entity_kind(
    iri: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<ProfileEntityKind>> {
    for (kind, values) in [
        (ProfileEntityKind::Class, BUILTIN_CLASSES),
        (ProfileEntityKind::ObjectProperty, BUILTIN_OBJECT_PROPERTIES),
        (ProfileEntityKind::DataProperty, BUILTIN_DATA_PROPERTIES),
        (
            ProfileEntityKind::AnnotationProperty,
            BUILTIN_ANNOTATION_PROPERTIES,
        ),
        (ProfileEntityKind::Datatype, BUILTIN_DATATYPES),
    ] {
        for value in values {
            budget.claim_work(1)?;
            if iri == *value {
                return Ok(Some(kind));
            }
        }
    }
    Ok(None)
}

fn anonymous_assertion_endpoints<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Option<AnonymousKey>, Option<AnonymousKey>)> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_PROPERTY_ASSERTION_TAG || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "validated object-property assertion lost its schema-1 shape",
        ));
    }
    let fields = node.fields();
    let source_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let target_field = fields
        .start
        .checked_add(2)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let source = required_node(model, source_field, "profile object-assertion source")?;
    let target = required_node(model, target_field, "profile object-assertion target")?;
    Ok((
        anonymous_endpoint(model, source, scope_maps, budget)?,
        anonymous_endpoint(model, target, scope_maps, budget)?,
    ))
}

fn anonymous_endpoint<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AnonymousKey>> {
    match model.node(identifier)?.tag() {
        ANONYMOUS_INDIVIDUAL_TAG => anonymous_key(model, identifier, scope_maps, budget).map(Some),
        ENTITY_TAG => Ok(None),
        _ => Err(EncodedValidationError::invariant(
            "validated object-property assertion endpoint is not an individual",
        )),
    }
}

fn anonymous_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<AnonymousKey> {
    let node = model.node(identifier)?;
    if node.tag() != ANONYMOUS_INDIVIDUAL_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated anonymous individual lost its schema-1 shape",
        ));
    }
    let fields = node.fields();
    let scope = fixed_profile_bytes(
        model,
        fields.start,
        "profile anonymous document scope",
        budget,
    )?;
    let local_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let local = fixed_profile_bytes(model, local_field, "profile anonymous local key", budget)?;
    let scope = canonical::remap_anonymous_scope(scope, scope_maps, budget)?;
    let mut key = [0_u8; 64];
    key[..32].copy_from_slice(&scope);
    key[32..].copy_from_slice(&local);
    Ok(key)
}

fn fixed_profile_bytes<B: ByteSource>(
    model: &ValidatedModel<B>,
    field_index: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Scalar(value) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated encoded {name} is not scalar"
        )));
    };
    if value.kind() != ComponentKind::Bytes || value.len() != 32 {
        return Err(EncodedValidationError::invariant(format!(
            "validated encoded {name} is not a 32-byte value"
        )));
    }
    budget.claim_work(32)?;
    let mut result = [0_u8; 32];
    for (index, target) in result.iter_mut().enumerate() {
        *target = value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant(format!("validated encoded {name} disappeared"))
        })?;
    }
    Ok(result)
}

fn append_anonymous_graph_issues<E>(
    vertices: &[AnonymousKey],
    assertions: &[AnonymousAssertion],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if vertices.is_empty() {
        return Ok(());
    }
    poll(control, "profile-anonymous-graph-preflight")?;
    let index_bytes = vertices
        .len()
        .checked_mul(size_of::<usize>())
        .ok_or_else(|| {
            EncodedValidationError::resource("profile anonymous graph index size overflowed")
        })?;

    budget.claim_owned(index_bytes)?;
    let mut parent = Vec::new();
    reserve_exact(
        &mut parent,
        vertices.len(),
        "profile anonymous parent allocation failed",
    )?;
    parent.extend(0..vertices.len());

    budget.claim_owned(index_bytes)?;
    let mut named_link_counts = Vec::new();
    reserve_exact(
        &mut named_link_counts,
        vertices.len(),
        "profile anonymous named-link count allocation failed",
    )?;
    named_link_counts.resize(vertices.len(), 0_usize);

    budget.claim_owned(index_bytes)?;
    let mut named_link_representatives = Vec::new();
    reserve_exact(
        &mut named_link_representatives,
        vertices.len(),
        "profile anonymous named-link representative allocation failed",
    )?;
    named_link_representatives.resize(vertices.len(), usize::MAX);

    let parallel_bytes = assertions
        .len()
        .checked_mul(size_of::<(usize, usize, usize)>())
        .ok_or_else(|| {
            EncodedValidationError::resource("profile anonymous parallel-edge size overflowed")
        })?;
    budget.claim_owned(parallel_bytes)?;
    let mut parallel_edges = Vec::new();
    reserve_exact(
        &mut parallel_edges,
        assertions.len(),
        "profile anonymous parallel-edge allocation failed",
    )?;

    for (assertion_index, assertion) in assertions.iter().enumerate() {
        poll(control, "profile-anonymous-assertion")?;
        budget.claim_work(1)?;
        match (assertion.source, assertion.target) {
            (Some(source), Some(target)) => {
                let source_index = anonymous_index(vertices, &source, budget)?;
                let target_index = anonymous_index(vertices, &target, budget)?;
                let pair = if source_index <= target_index {
                    (source_index, target_index, assertion_index)
                } else {
                    (target_index, source_index, assertion_index)
                };
                parallel_edges.push(pair);
                let source_root = anonymous_root(&mut parent, source_index, budget)?;
                let target_root = anonymous_root(&mut parent, target_index, budget)?;
                if source_root == target_root {
                    push_profile_issue(
                        issues,
                        ProfileIssue {
                            rule_id: ANONYMOUS_GRAPH_CYCLE_RULE,
                            severity: "error",
                            message: Cow::Borrowed(ANONYMOUS_GRAPH_CYCLE_MESSAGE),
                            constructor: Some("ObjectPropertyAssertion"),
                            provenance_sha256: Some(assertion.provenance_sha256),
                        },
                        budget,
                    )?;
                } else {
                    parent[target_root] = source_root;
                }
            }
            (Some(value), None) | (None, Some(value)) => {
                let index = anonymous_index(vertices, &value, budget)?;
                named_link_counts[index] =
                    named_link_counts[index].checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "profile anonymous named-link count overflowed",
                        )
                    })?;
                if named_link_representatives[index] == usize::MAX {
                    named_link_representatives[index] = assertion_index;
                }
            }
            (None, None) => {
                return Err(EncodedValidationError::invariant(
                    "profile anonymous assertion contains no anonymous endpoint",
                )
                .into());
            }
        }
    }

    budget.claim_work(sort_work(parallel_edges.len()))?;
    parallel_edges.sort_unstable();
    let mut start = 0_usize;
    while start < parallel_edges.len() {
        let mut end = start + 1;
        while end < parallel_edges.len()
            && parallel_edges[end].0 == parallel_edges[start].0
            && parallel_edges[end].1 == parallel_edges[start].1
        {
            budget.claim_work(1)?;
            end += 1;
        }
        if end - start > 1 {
            let assertion = assertions.get(parallel_edges[start].2).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "profile parallel-edge representative is out of range",
                )
            })?;
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: ANONYMOUS_PARALLEL_EDGE_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_PARALLEL_EDGE_MESSAGE),
                    constructor: Some("ObjectPropertyAssertion"),
                    provenance_sha256: Some(assertion.provenance_sha256),
                },
                budget,
            )?;
        }
        start = end;
    }

    budget.claim_owned(index_bytes)?;
    let mut component_by_vertex = Vec::new();
    reserve_exact(
        &mut component_by_vertex,
        vertices.len(),
        "profile anonymous component allocation failed",
    )?;
    budget.claim_owned(index_bytes)?;
    let mut component_roots = Vec::new();
    reserve_exact(
        &mut component_roots,
        vertices.len(),
        "profile anonymous component-root allocation failed",
    )?;
    for vertex in 0..vertices.len() {
        let root = anonymous_root(&mut parent, vertex, budget)?;
        component_by_vertex.push(root);
        component_roots.push(root);
    }
    budget.claim_work(sort_work(component_roots.len()))?;
    component_roots.sort_unstable();
    component_roots.dedup();

    for component_root in component_roots {
        poll(control, "profile-anonymous-component")?;
        let mut representative = usize::MAX;
        let mut valid = true;
        for (vertex, root) in component_by_vertex.iter().copied().enumerate() {
            budget.claim_work(1)?;
            if root != component_root {
                continue;
            }
            if named_link_counts[vertex] <= 1 {
                valid = false;
                break;
            }
            representative = representative.min(named_link_representatives[vertex]);
        }
        if valid {
            let assertion = assertions.get(representative).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "profile anonymous tree-root representative is out of range",
                )
            })?;
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: ANONYMOUS_TREE_ROOT_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_TREE_ROOT_MESSAGE),
                    constructor: Some("ObjectPropertyAssertion"),
                    provenance_sha256: Some(assertion.provenance_sha256),
                },
                budget,
            )?;
        }
    }
    poll(control, "profile-anonymous-graph-complete")?;
    Ok(())
}

fn anonymous_index(
    vertices: &[AnonymousKey],
    value: &AnonymousKey,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    budget.claim_work(search_work(vertices.len()))?;
    vertices.binary_search(value).map_err(|_| {
        EncodedValidationError::invariant(
            "profile anonymous assertion references a missing graph vertex",
        )
    })
}

fn anonymous_root(
    parent: &mut [usize],
    start: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    let mut current = start;
    loop {
        budget.claim_work(1)?;
        let following = *parent.get(current).ok_or_else(|| {
            EncodedValidationError::invariant("profile anonymous parent index is out of range")
        })?;
        if following == current {
            break;
        }
        current = following;
    }
    let root = current;
    current = start;
    while parent[current] != current {
        budget.claim_work(1)?;
        let following = parent[current];
        parent[current] = root;
        current = following;
    }
    Ok(root)
}

fn is_recomputed_profile_rule(rule_id: &str) -> bool {
    matches!(
        rule_id,
        ANONYMOUS_GRAPH_CYCLE_RULE
            | ANONYMOUS_PARALLEL_EDGE_RULE
            | ANONYMOUS_TREE_ROOT_RULE
            | PROPERTY_PUNNING_RULE
            | CLASS_DATATYPE_PUNNING_RULE
            | RESERVED_VOCABULARY_RULE
            | BUILTIN_ENTITY_KIND_RULE
            | MISSING_DECLARATION_RULE
    )
}

fn push_profile_issue(
    issues: &mut Vec<ProfileIssue>,
    issue: ProfileIssue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = issues
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile issue count overflowed"))?;
    budget.claim_issue(following)?;
    reserve_profile_one(issues, budget, "profile issue allocation failed")?;
    issues.push(issue);
    Ok(())
}

fn clone_profile_bytes(
    value: &[u8],
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<Vec<u8>> {
    budget.claim_owned(value.len())?;
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(message))?;
    owned.extend_from_slice(value);
    Ok(owned)
}

fn reserve_profile_one<T>(
    values: &mut Vec<T>,
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<()> {
    if values.len() < values.capacity() {
        return Ok(());
    }
    let following_capacity = if values.capacity() == 0 {
        4
    } else {
        values
            .capacity()
            .checked_mul(2)
            .ok_or_else(|| EncodedValidationError::resource("profile capacity overflowed"))?
    };
    let additional = following_capacity - values.capacity();
    budget.claim_owned(
        additional.checked_mul(size_of::<T>()).ok_or_else(|| {
            EncodedValidationError::resource("profile allocation size overflowed")
        })?,
    )?;
    values
        .try_reserve_exact(additional)
        .map_err(|_| EncodedValidationError::resource(message))
}

fn forbidden_anonymous_expression<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<&'static str>> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    match node.tag() {
        OBJECT_ONE_OF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf lost its schema-1 shape",
                ));
            }
            let component =
                required_component(model.field(node.fields().start)?, "profile nominal members")?;
            let ComponentValue::Collection(members) = model.resolve(component)? else {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf members are not a collection",
                ));
            };
            if members.kind() != ComponentKind::Set {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf members are not a canonical set",
                ));
            }
            for item_index in members.items() {
                budget.claim_work(1)?;
                let component =
                    required_component(model.item(item_index)?, "profile nominal member")?;
                let ComponentValue::Node(member) = model.resolve(component)? else {
                    return Err(EncodedValidationError::invariant(
                        "validated ObjectOneOf member is not a node",
                    ));
                };
                if model.node(member)?.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                    return Ok(Some("ObjectOneOf"));
                }
            }
            Ok(None)
        }
        OBJECT_HAS_VALUE_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectHasValue lost its schema-1 shape",
                ));
            }
            let value_field = node.fields().start.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("profile field index overflowed")
            })?;
            let value = required_node(model, value_field, "profile ObjectHasValue value")?;
            if model.node(value)?.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                Ok(Some("ObjectHasValue"))
            } else {
                Ok(None)
            }
        }
        _ => Err(EncodedValidationError::invariant(
            "profile anonymous-expression dispatch received a different constructor",
        )),
    }
}

fn allows_top_data_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != SUB_DATA_PROPERTY_TAG {
        return Ok(false);
    }
    if node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "validated data subproperty axiom lost its schema-1 shape",
        ));
    }
    let fields = node.fields();
    let sub_property = required_node(model, fields.start, "profile data subproperty expression")?;
    let super_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let super_property =
        required_node(model, super_field, "profile data super-property expression")?;
    if !is_top_data_property(model, super_property, budget)? {
        return Ok(false);
    }
    Ok(!is_top_data_property(model, sub_property, budget)?)
}

fn is_top_data_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    budget.claim_work(5)?;
    let entity = model.node(identifier)?;
    if entity.tag() != ENTITY_TAG || entity.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity lost its schema-1 shape",
        ));
    }
    let fields = entity.fields();
    let kind_component = required_component(model.field(fields.start)?, "profile entity kind")?;
    let ComponentValue::Scalar(kind) = model.resolve(kind_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not scalar",
        ));
    };
    if kind.kind() != ComponentKind::Enum {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not an enum",
        ));
    }
    if !kind.bytes_equal(b"data_property") {
        return Ok(false);
    }
    let iri_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity field index overflowed"))?;
    let iri_identifier = required_node(model, iri_field, "profile entity IRI")?;
    let iri = model.node(iri_identifier)?;
    if iri.tag() != IRI_TAG || iri.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI lost its schema-1 shape",
        ));
    }
    let text_component =
        required_component(model.field(iri.fields().start)?, "profile entity IRI text")?;
    let ComponentValue::Scalar(text) = model.resolve(text_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI text is not scalar",
        ));
    };
    if text.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI is not text",
        ));
    }
    Ok(text.bytes_equal(TOP_DATA_PROPERTY_IRI))
}

fn required_node<B: ByteSource>(
    model: &ValidatedModel<B>,
    field_index: usize,
    name: &'static str,
) -> EncodedResult<NodeId> {
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated encoded {name} is not a node"
        )));
    };
    Ok(identifier)
}

fn enqueue_component<B: ByteSource>(
    model: &ValidatedModel<B>,
    component: ComponentRef,
    marks: &mut [u32],
    epoch: u32,
    stack: &mut Vec<NodeId>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    match model.resolve(component)? {
        ComponentValue::Node(identifier) => enqueue_node(identifier, marks, epoch, stack),
        ComponentValue::Collection(collection) => {
            for item_index in collection.items() {
                budget.claim_work(1)?;
                let item = required_component(model.item(item_index)?, "profile collection item")?;
                if let ComponentValue::Node(identifier) = model.resolve(item)? {
                    enqueue_node(identifier, marks, epoch, stack)?;
                }
            }
            Ok(())
        }
        ComponentValue::None | ComponentValue::Scalar(_) => Ok(()),
    }
}

fn enqueue_node(
    identifier: NodeId,
    marks: &mut [u32],
    epoch: u32,
    stack: &mut Vec<NodeId>,
) -> EncodedResult<()> {
    let index = usize::try_from(identifier.get() - 1).map_err(|_| {
        EncodedValidationError::invariant("profile node index exceeds the platform width")
    })?;
    let mark = marks.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("profile node identifier is out of range")
    })?;
    if *mark != epoch {
        *mark = epoch;
        stack.push(identifier);
    }
    Ok(())
}

fn validate_phase(phase: &ProfilePhase) -> EncodedResult<()> {
    if phase.conforms != phase.issues.is_empty() {
        return Err(EncodedValidationError::invariant(
            "profile conformance flag diverges from its issues",
        ));
    }
    if phase.axioms_checked != phase.axiom_keys.len() {
        return Err(EncodedValidationError::invariant(
            "profile checked-axiom count diverges from its canonical keys",
        ));
    }
    if phase.extensions_checked != phase.extension_keys.len() {
        return Err(EncodedValidationError::invariant(
            "profile checked-extension count diverges from its canonical keys",
        ));
    }
    if phase.issues.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile issues are not canonical sorted unique",
        ));
    }
    if phase.axiom_keys.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile axiom keys are not canonical sorted unique",
        ));
    }
    if phase
        .extension_keys
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile extension keys are not canonical sorted unique",
        ));
    }
    if phase
        .anonymous_vertices
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile anonymous vertices are not canonical sorted unique",
        ));
    }
    if phase
        .anonymous_assertions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile anonymous assertions are not canonical sorted unique",
        ));
    }
    if phase.entity_uses.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile entity uses are not canonical sorted unique",
        ));
    }
    if phase
        .entity_declarations
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile entity declarations are not canonical sorted unique",
        ));
    }
    Ok(())
}

fn required_component(
    component: Option<ComponentRef>,
    name: &'static str,
) -> EncodedResult<ComponentRef> {
    component.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated encoded {name} disappeared"))
    })
}

fn poll<E>(
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
    phase: &'static str,
) -> ControlledResult<(), E> {
    control(phase).map_err(ProfilePhaseError::Control)
}

fn into_encoded<T>(result: ControlledResult<T, Infallible>) -> EncodedResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(ProfilePhaseError::Encoded(error)) => Err(error),
        Err(ProfilePhaseError::Control(never)) => match never {},
    }
}

fn reserve_exact<T>(
    values: &mut Vec<T>,
    additional: usize,
    message: &'static str,
) -> EncodedResult<()> {
    values
        .try_reserve_exact(additional)
        .map_err(|_| EncodedValidationError::resource(message))
}

fn reserve_one<T>(values: &mut Vec<T>, message: &'static str) -> EncodedResult<()> {
    if values.len() == values.capacity() {
        values
            .try_reserve_exact(1)
            .map_err(|_| EncodedValidationError::resource(message))?;
    }
    Ok(())
}

fn sort_work(count: usize) -> usize {
    if count < 2 {
        return count;
    }
    let rounds = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(rounds).unwrap_or(usize::MAX))
}

fn search_work(count: usize) -> usize {
    if count < 2 {
        return 1;
    }
    usize::try_from(usize::BITS - (count - 1).leading_zeros()).unwrap_or(usize::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoded::{EncodedColumns, EncodedLimits};

    #[derive(Clone, Copy)]
    struct Bytes<'a>(&'a [u8]);

    impl ByteSource for Bytes<'_> {
        fn len(self) -> usize {
            self.0.len()
        }

        fn byte(self, index: usize) -> Option<u8> {
            self.0.get(index).copied()
        }
    }

    #[derive(Clone, Debug)]
    struct OwnedColumns {
        root_kinds: Vec<u8>,
        root_ids: Vec<u8>,
        node_tags: Vec<u8>,
        node_field_offsets: Vec<u8>,
        field_kinds: Vec<u8>,
        field_values: Vec<u8>,
        field_lengths: Vec<u8>,
        item_kinds: Vec<u8>,
        item_values: Vec<u8>,
        item_lengths: Vec<u8>,
        scalar_bytes: Vec<u8>,
    }

    impl OwnedColumns {
        fn borrowed(&self) -> EncodedColumns<Bytes<'_>> {
            EncodedColumns {
                root_kinds: Bytes(&self.root_kinds),
                root_ids: Bytes(&self.root_ids),
                node_tags: Bytes(&self.node_tags),
                node_field_offsets: Bytes(&self.node_field_offsets),
                field_kinds: Bytes(&self.field_kinds),
                field_values: Bytes(&self.field_values),
                field_lengths: Bytes(&self.field_lengths),
                item_kinds: Bytes(&self.item_kinds),
                item_values: Bytes(&self.item_values),
                item_lengths: Bytes(&self.item_lengths),
                scalar_bytes: Bytes(&self.scalar_bytes),
            }
        }
    }

    fn le16(values: &[u16]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le32(values: &[u32]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le64(values: &[u64]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn invalid_data_arity_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2, 2, 2, 2],
            root_ids: le32(&[10, 11, 12, 13]),
            node_tags: le16(&[1, 1, 1, 1, 2, 2, 2, 2, 41, 60, 60, 60, 61]),
            node_field_offsets: le64(&[0, 1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 23]),
            field_kinds: vec![
                2, 2, 2, 2, 5, 1, 5, 1, 5, 1, 5, 1, 7, 1, 1, 6, 1, 6, 1, 6, 1, 1, 6,
            ],
            field_values: le64(&[
                0, 18, 36, 54, 93, 1, 98, 4, 106, 2, 119, 3, 0, 6, 5, 2, 7, 2, 8, 2, 5, 9, 2,
            ]),
            field_lengths: le64(&[
                18, 18, 18, 39, 5, 0, 8, 0, 13, 0, 13, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ]),
            item_kinds: vec![1, 1],
            item_values: le64(&[7, 8]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes: concat!(
                "urn:test:profile#A",
                "urn:test:profile#p",
                "urn:test:profile#q",
                "http://www.w3.org/2001/XMLSchema#string",
                "class",
                "datatype",
                "data_property",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn invalid_top_data_property_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[3]),
            node_tags: le16(&[IRI_TAG, ENTITY_TAG, 95]),
            node_field_offsets: le64(&[0, 1, 3, 5]),
            field_kinds: vec![2, 5, 1, 1, 6],
            field_values: le64(&[0, 45, 1, 2, 0]),
            field_lengths: le64(&[45, 13, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: concat!(
                "http://www.w3.org/2002/07/owl#topDataProperty",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn allowed_top_data_property_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[5]),
            node_tags: le16(&[
                IRI_TAG,
                IRI_TAG,
                ENTITY_TAG,
                ENTITY_TAG,
                SUB_DATA_PROPERTY_TAG,
            ]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 9]),
            field_kinds: vec![2, 2, 5, 1, 5, 1, 1, 1, 6],
            field_values: le64(&[0, 10, 55, 1, 68, 2, 3, 4, 0]),
            field_lengths: le64(&[10, 45, 13, 0, 13, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: concat!(
                "urn:test#p",
                "http://www.w3.org/2002/07/owl#topDataProperty",
                "data_property",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn anonymous_forbidden_columns() -> OwnedColumns {
        let mut scalar_bytes = concat!("urn:test#named", "named_individual")
            .as_bytes()
            .to_vec();
        scalar_bytes.extend_from_slice(&[0x11; 32]);
        scalar_bytes.extend_from_slice(&[0x22; 32]);
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[4]),
            node_tags: le16(&[
                IRI_TAG,
                ENTITY_TAG,
                ANONYMOUS_INDIVIDUAL_TAG,
                DIFFERENT_INDIVIDUALS_TAG,
            ]),
            node_field_offsets: le64(&[0, 1, 3, 5, 7]),
            field_kinds: vec![2, 5, 1, 3, 3, 6, 6],
            field_values: le64(&[0, 14, 1, 30, 62, 0, 2]),
            field_lengths: le64(&[14, 16, 0, 32, 32, 2, 0]),
            item_kinds: vec![1, 1],
            item_values: le64(&[2, 3]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes,
        }
    }

    fn extension_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![3],
            root_ids: le32(&[1]),
            node_tags: le16(&[SWRL_RULE_TAG]),
            node_field_offsets: le64(&[0, 3]),
            field_kinds: vec![6, 6, 6],
            field_values: le64(&[0, 0, 0]),
            field_lengths: le64(&[0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: Vec::new(),
        }
    }

    fn model(columns: &OwnedColumns) -> EncodedResult<ValidatedModel<Bytes<'_>>> {
        ValidatedModel::new(columns.borrowed(), EncodedLimits::default())
    }

    #[test]
    fn data_range_arity_issue_and_provenance_are_exact() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 4);
        assert_eq!(phase.extensions_checked, 0);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, DATA_RANGE_ARITY_RULE);
        assert_eq!(phase.issues[0].constructor, Some("DataSomeValuesFrom"));
        assert_eq!(
            phase.issues[0]
                .provenance_sha256
                .map(|value| crate::model::hex(&value))
                .as_deref(),
            Some("6a1bfbadd77d1f86ac453a99501c3f363d5b71f420e67ade72d564f590a16aa7")
        );
        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("profile manifest is not JSON"))?;
        assert_eq!(manifest["family"], "owl2_dl_profile");
        assert_eq!(manifest["ordered_rule_ids"][0], DATA_RANGE_ARITY_RULE);
        Ok(())
    }

    #[test]
    fn top_data_property_position_is_exact_and_preserves_the_valid_super_position(
    ) -> EncodedResult<()> {
        let invalid = invalid_top_data_property_columns();
        let phase = compile_profile_phase(&model(&invalid)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, TOP_DATA_PROPERTY_RULE);
        assert_eq!(phase.issues[0].constructor, Some("FunctionalDataProperty"));
        assert_eq!(
            phase.issues[0]
                .provenance_sha256
                .map(|value| crate::model::hex(&value))
                .as_deref(),
            Some("721e62a719bbd8248bd2494e9eb90cc60408328ad18fb008d082902082eb6a4d")
        );

        let allowed = allowed_top_data_property_columns();
        let allowed_phase =
            compile_profile_phase(&model(&allowed)?, &[], ProfilePhaseLimits::default())?;
        assert!(!allowed_phase.conforms);
        assert_eq!(allowed_phase.axioms_checked, 1);
        assert_eq!(allowed_phase.issues.len(), 1);
        assert_eq!(allowed_phase.issues[0].rule_id, MISSING_DECLARATION_RULE);
        Ok(())
    }

    #[test]
    fn anonymous_axiom_position_is_exact_and_scope_sensitive() -> EncodedResult<()> {
        let columns = anonymous_forbidden_columns();
        let model = model(&columns)?;
        let phase = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, ANONYMOUS_AXIOM_POSITION_RULE);
        assert_eq!(phase.issues[0].constructor, Some("DifferentIndividuals"));

        let scope_maps = vec![vec![canonical::AnonymousScopeReplacement {
            source: [0x11; 32],
            target: [0x33; 32],
        }]];
        let mapped = compile_profile_phase(&model, &scope_maps, ProfilePhaseLimits::default())?;
        assert_eq!(mapped.issues.len(), 1);
        assert_ne!(
            mapped.issues[0].provenance_sha256,
            phase.issues[0].provenance_sha256
        );
        Ok(())
    }

    #[test]
    fn anonymous_graph_rules_use_global_canonical_assertion_order() -> EncodedResult<()> {
        let vertex = |value| [value; 64];
        let assertion = |order: u8, provenance: u8, source: Option<u8>, target: Option<u8>| {
            AnonymousAssertion {
                axiom_key: vec![order],
                provenance_sha256: [provenance; 32],
                source: source.map(vertex),
                target: target.map(vertex),
            }
        };
        let vertices = vec![
            vertex(1),
            vertex(2),
            vertex(3),
            vertex(4),
            vertex(5),
            vertex(6),
        ];
        let assertions = vec![
            assertion(1, 1, Some(1), Some(2)),
            assertion(2, 2, Some(2), Some(3)),
            assertion(3, 3, Some(3), Some(1)),
            assertion(4, 4, Some(4), Some(5)),
            assertion(5, 5, Some(5), Some(4)),
            assertion(6, 6, Some(6), None),
            assertion(7, 7, None, Some(6)),
        ];
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();

        assert_eq!(issues.len(), 4);
        assert_eq!(
            issues
                .iter()
                .filter(|issue| issue.rule_id == ANONYMOUS_GRAPH_CYCLE_RULE)
                .filter_map(|issue| issue.provenance_sha256.map(|value| value[0]))
                .collect::<Vec<_>>(),
            vec![3, 5]
        );
        assert_eq!(
            issues
                .iter()
                .find(|issue| issue.rule_id == ANONYMOUS_PARALLEL_EDGE_RULE)
                .and_then(|issue| issue.provenance_sha256.map(|value| value[0])),
            Some(4)
        );
        assert_eq!(
            issues
                .iter()
                .find(|issue| issue.rule_id == ANONYMOUS_TREE_ROOT_RULE)
                .and_then(|issue| issue.provenance_sha256.map(|value| value[0])),
            Some(6)
        );

        let mut cancelled_issues = Vec::new();
        let mut cancelled_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let cancelled = append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut cancelled_issues,
            &mut cancelled_budget,
            &mut |phase| {
                if phase == "profile-anonymous-assertion" {
                    Err("injected graph cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected graph cancellation"))
        );
        assert!(cancelled_issues.is_empty());

        let mut limited_issues = Vec::new();
        let mut limited_budget = PhaseBudget::new(ProfilePhaseLimits {
            max_issues: 0,
            ..ProfilePhaseLimits::default()
        });
        let limited = append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut limited_issues,
            &mut limited_budget,
            &mut control,
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "anonymous graph issue limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert!(limited_issues.is_empty());
        Ok(())
    }

    #[test]
    fn global_entity_rules_use_merged_kind_and_declaration_facts() -> EncodedResult<()> {
        let identity = |iri: &str, kind| ProfileEntityIdentity {
            iri: iri.as_bytes().to_vec(),
            kind,
        };
        let mut uses = vec![
            identity(
                "http://www.w3.org/1999/02/22-rdf-syntax-ns#custom",
                ProfileEntityKind::Class,
            ),
            identity(
                "http://www.w3.org/2002/07/owl#real",
                ProfileEntityKind::Class,
            ),
            identity("urn:annotation", ProfileEntityKind::AnnotationProperty),
            identity("urn:dual", ProfileEntityKind::Class),
            identity("urn:dual", ProfileEntityKind::Datatype),
            identity("urn:missing", ProfileEntityKind::Class),
            identity("urn:named", ProfileEntityKind::NamedIndividual),
            identity("urn:shared", ProfileEntityKind::DataProperty),
            identity("urn:shared", ProfileEntityKind::ObjectProperty),
        ];
        uses.sort();
        let mut declarations = vec![
            uses[0].clone(),
            uses[1].clone(),
            identity("urn:dual", ProfileEntityKind::Class),
            identity("urn:dual", ProfileEntityKind::Datatype),
            identity("urn:shared", ProfileEntityKind::DataProperty),
            identity("urn:shared", ProfileEntityKind::ObjectProperty),
        ];
        declarations.sort();
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_entity_issues(
            &uses,
            &declarations,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();

        assert_eq!(issues.len(), 6);
        assert_eq!(
            issues
                .iter()
                .filter(|issue| issue.rule_id == MISSING_DECLARATION_RULE)
                .count(),
            2
        );
        assert_eq!(
            issues
                .iter()
                .map(|issue| issue.rule_id)
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from([
                BUILTIN_ENTITY_KIND_RULE,
                CLASS_DATATYPE_PUNNING_RULE,
                MISSING_DECLARATION_RULE,
                PROPERTY_PUNNING_RULE,
                RESERVED_VOCABULARY_RULE,
            ])
        );
        assert!(issues
            .iter()
            .all(|issue| issue.constructor.is_none() && issue.provenance_sha256.is_none()));

        let mut cancelled_issues = Vec::new();
        let mut cancelled_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let cancelled = append_entity_issues(
            &uses,
            &declarations,
            &mut cancelled_issues,
            &mut cancelled_budget,
            &mut |phase| {
                if phase == "profile-entity-iri" {
                    Err("injected entity cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected entity cancellation"))
        );
        assert!(cancelled_issues.is_empty());
        Ok(())
    }

    #[test]
    fn extension_issue_provenance_and_count_are_exact() -> EncodedResult<()> {
        let columns = extension_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 0);
        assert_eq!(phase.extensions_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, EXTENSION_COMPONENT_RULE);
        assert_eq!(phase.issues[0].constructor, Some("SWRLRule"));

        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("profile manifest is not JSON"))?;
        assert_eq!(manifest["extensions_checked"], 1);
        assert_eq!(manifest["ordered_rule_ids"][0], EXTENSION_COMPONENT_RULE);

        let merged =
            merge_profile_phases(vec![phase.clone(), phase], ProfilePhaseLimits::default())?;
        assert_eq!(merged.extensions_checked, 1);
        assert_eq!(merged.issues.len(), 1);

        let limited = ProfilePhaseLimits {
            max_extensions: 0,
            ..ProfilePhaseLimits::default()
        };
        let error = compile_profile_phase(&model(&columns)?, &[], limited)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant("profile extension limit unexpectedly succeeded")
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }

    #[test]
    fn include_exclude_selection_and_merge_are_canonical() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let model = model(&columns)?;
        let mut control = |_phase| Ok::<(), Infallible>(());
        let included = into_encoded(compile_profile_phase_selected_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            POSTINGS_INCLUDE,
            4_u32.to_le_bytes().as_slice(),
            &mut control,
        ))?;
        assert_eq!(included.axioms_checked, 1);
        assert_eq!(included.extensions_checked, 0);
        assert_eq!(included.issues.len(), 4);
        assert_eq!(
            included
                .issues
                .iter()
                .filter(|issue| issue.rule_id == DATA_RANGE_ARITY_RULE)
                .count(),
            1
        );
        assert_eq!(
            included
                .issues
                .iter()
                .filter(|issue| issue.rule_id == MISSING_DECLARATION_RULE)
                .count(),
            3
        );
        let excluded = into_encoded(compile_profile_phase_selected_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            POSTINGS_EXCLUDE,
            4_u32.to_le_bytes().as_slice(),
            &mut control,
        ))?;
        assert_eq!(excluded.axioms_checked, 3);
        assert!(excluded.conforms);

        let left = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        let right = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        let merged = merge_profile_phases(
            vec![left.clone(), right.clone()],
            ProfilePhaseLimits::default(),
        )?;
        let reversed = merge_profile_phases(vec![right, left], ProfilePhaseLimits::default())?;
        assert_eq!(
            merged.canonical_manifest_json()?,
            reversed.canonical_manifest_json()?
        );
        assert_eq!(merged.axioms_checked, 4);
        assert_eq!(merged.extensions_checked, 0);
        assert_eq!(merged.issues.len(), 1);
        Ok(())
    }

    #[test]
    fn cancellation_and_resource_failure_leave_retry_available() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let model = model(&columns)?;
        let mut polls = 0_usize;
        let result = compile_profile_phase_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            &mut |_phase| {
                polls += 1;
                if polls == 3 {
                    Err("injected cancellation")
                } else {
                    Ok(())
                }
            },
        );
        let Err(error) = result else {
            return Err(EncodedValidationError::invariant(
                "profile cancellation unexpectedly succeeded",
            ));
        };
        assert_eq!(error, ProfilePhaseError::Control("injected cancellation"));

        let limited = ProfilePhaseLimits {
            max_issues: 0,
            ..ProfilePhaseLimits::default()
        };
        let error = compile_profile_phase(&model, &[], limited)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant("profile issue limit unexpectedly succeeded")
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let retry = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        assert_eq!(retry.issues.len(), 1);
        Ok(())
    }

    #[test]
    fn allocation_and_manifest_limits_are_fallible() -> EncodedResult<()> {
        let mut values = Vec::<u8>::new();
        let error = reserve_exact(
            &mut values,
            usize::MAX,
            "injected profile allocation failure",
        )
        .err()
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "impossible profile allocation unexpectedly succeeded",
            )
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert_eq!(error.message, "injected profile allocation failure");

        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(
            &model(&columns)?,
            &[],
            ProfilePhaseLimits {
                max_manifest_bytes: 1,
                ..ProfilePhaseLimits::default()
            },
        )?;
        let error = phase.canonical_manifest_json().err().ok_or_else(|| {
            EncodedValidationError::invariant("profile manifest limit unexpectedly succeeded")
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        for limited in [
            ProfilePhaseLimits {
                max_entity_uses: 0,
                ..ProfilePhaseLimits::default()
            },
            ProfilePhaseLimits {
                max_entity_declarations: 0,
                ..ProfilePhaseLimits::default()
            },
        ] {
            let error = compile_profile_phase(&model(&columns)?, &[], limited)
                .err()
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "profile entity fact limit unexpectedly succeeded",
                    )
                })?;
            assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        }
        Ok(())
    }
}
