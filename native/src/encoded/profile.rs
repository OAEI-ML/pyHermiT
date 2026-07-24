//! Bounded OWL 2 DL profile diagnostics over encoded structural input.
//!
//! Profile violations are successful semantic output. Malformed columns,
//! resource exhaustion, and cancellation remain distinct operational failures.
//! This first private phase owns exact data-arity, top-data-property, and
//! extension projections. Structural-columns schema 1 does not carry
//! document-origin rows, so the manifest exposes canonical root provenance without inventing
//! `ProfileIssue.document_keys`. Issue ordering and deduplication therefore use
//! the exact projected field tuple published by this phase.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::convert::Infallible;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::canonical::{self, AnonymousScopeMap, CanonicalBudget};
use super::model::{ComponentKind, ComponentRef, ComponentValue, NodeId, RootKind, ValidatedModel};
use super::symbols::RootHandler;
use super::{u32_at, ByteSource, EncodedResult, EncodedValidationError};

const PROFILE_PHASE_SCHEMA_VERSION: u16 = 1;
const POSTINGS_ALL: u8 = 0;
const POSTINGS_INCLUDE: u8 = 1;
const POSTINGS_EXCLUDE: u8 = 2;
const IRI_TAG: u16 = 1;
const ENTITY_TAG: u16 = 2;
const DATA_SOME_VALUES_FROM_TAG: u16 = 41;
const DATA_ALL_VALUES_FROM_TAG: u16 = 42;
const SUB_DATA_PROPERTY_TAG: u16 = 90;
const SWRL_RULE_TAG: u16 = 148;
const TOP_DATA_PROPERTY_IRI: &[u8] = b"http://www.w3.org/2002/07/owl#topDataProperty";
const DATA_RANGE_ARITY_RULE: &str = "OWL2_DATA_RANGE_ARITY";
const DATA_RANGE_ARITY_MESSAGE: &str =
    "OWL 2 defines only unary data ranges, so the restriction must use exactly one data property";
const TOP_DATA_PROPERTY_RULE: &str = "OWL2DL_TOP_DATA_PROPERTY_POSITION";
const TOP_DATA_PROPERTY_MESSAGE: &str =
    "owl:topDataProperty may occur only as the super-property of a data subproperty axiom";
const EXTENSION_COMPONENT_RULE: &str = "OWL2DL_EXTENSION_COMPONENT";
const EXTENSION_COMPONENT_MESSAGE: &str =
    "extension components such as SWRL are outside the OWL 2 DL reasoner scope";
const PROFILE_MANIFEST_BASE_BOUND: usize = 256;
const PROFILE_MANIFEST_ISSUE_BOUND: usize = 640;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProfilePhaseLimits {
    pub max_slices: usize,
    pub max_axioms: usize,
    pub max_extensions: usize,
    pub max_issues: usize,
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
    pub message: &'static str,
    pub constructor: &'static str,
    pub provenance_sha256: [u8; 32],
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
    manifest_limit: usize,
}

impl ProfilePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase(self)?;
        let manifest_bound = self
            .issues
            .len()
            .checked_mul(PROFILE_MANIFEST_ISSUE_BOUND)
            .and_then(|issues| issues.checked_add(PROFILE_MANIFEST_BASE_BOUND))
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
        issues.extend(self.issues.iter().map(|issue| ProfileIssueManifest {
            rule_id: issue.rule_id,
            severity: issue.severity,
            message: issue.message,
            constructor: issue.constructor,
            provenance_sha256: crate::model::hex(&issue.provenance_sha256),
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
    constructor: &'a str,
    provenance_sha256: String,
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
            RootKind::OntologyAnnotation => continue,
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
                    message: EXTENSION_COMPONENT_MESSAGE,
                    constructor: "SWRLRule",
                    provenance_sha256,
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
        let top_data_property_allowed = allows_top_data_property(model, root.node(), &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;

        poll(control, "profile-provenance")?;
        let key = canonical::canonical_node_key(model, root.node(), scope_maps, &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work(key.len())
            .map_err(ProfilePhaseError::Encoded)?;
        let provenance_sha256: [u8; 32] = Sha256::digest(&key).into();
        axiom_keys.push(key);

        epoch = epoch.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile traversal epoch overflowed",
            ))
        })?;
        enqueue_node(root.node(), &mut marks, epoch, &mut stack)
            .map_err(ProfilePhaseError::Encoded)?;
        let mut top_data_property_occurs = false;
        while let Some(identifier) = stack.pop() {
            poll(control, "profile-node")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            let node = model.node(identifier).map_err(ProfilePhaseError::Encoded)?;
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
                        message: DATA_RANGE_ARITY_MESSAGE,
                        constructor: if node.tag() == DATA_SOME_VALUES_FROM_TAG {
                            "DataSomeValuesFrom"
                        } else {
                            "DataAllValuesFrom"
                        },
                        provenance_sha256,
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
                message: TOP_DATA_PROPERTY_MESSAGE,
                constructor: axiom_constructor,
                provenance_sha256,
            });
        }
    }

    poll(control, "profile-canonicalize")?;
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
        total.checked_add(phase.issues.len()).ok_or_else(|| {
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

    for mut phase in phases {
        validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work_u64(phase.work)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_owned(phase.owned_bytes)
            .map_err(ProfilePhaseError::Encoded)?;
        issues.append(&mut phase.issues);
        axiom_keys.append(&mut phase.axiom_keys);
        extension_keys.append(&mut phase.extension_keys);
        poll(control, "profile-merge-source")?;
    }
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
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-merge-complete")?;
    Ok(phase)
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
        assert_eq!(phase.issues[0].constructor, "DataSomeValuesFrom");
        assert_eq!(
            crate::model::hex(&phase.issues[0].provenance_sha256),
            "6a1bfbadd77d1f86ac453a99501c3f363d5b71f420e67ade72d564f590a16aa7"
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
        assert_eq!(phase.issues[0].constructor, "FunctionalDataProperty");
        assert_eq!(
            crate::model::hex(&phase.issues[0].provenance_sha256),
            "721e62a719bbd8248bd2494e9eb90cc60408328ad18fb008d082902082eb6a4d"
        );

        let allowed = allowed_top_data_property_columns();
        let allowed_phase =
            compile_profile_phase(&model(&allowed)?, &[], ProfilePhaseLimits::default())?;
        assert!(allowed_phase.conforms);
        assert_eq!(allowed_phase.axioms_checked, 1);
        assert!(allowed_phase.issues.is_empty());
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
        assert_eq!(phase.issues[0].constructor, "SWRLRule");

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
        assert_eq!(included.issues.len(), 1);
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
        Ok(())
    }
}
