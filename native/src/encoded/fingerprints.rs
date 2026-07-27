//! Authoritative pyowl-core fingerprints for one selected encoded view.
//!
//! This transaction is intentionally independent from the semantic symbol
//! domain.  Core signatures cover entities in ontology annotations, axiom
//! annotations, annotation axioms, and extensions, while the reasoner symbol
//! phase excludes those roots and injects private reasoning builtins.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use sha2::{Digest, Sha256};

use super::canonical::{
    self, annotation_stripped_node_key, canonical_node_key_with_entities, AnonymousScopeMap,
    CanonicalBudget,
};
use super::model::{RootKind, ValidatedModel};
use super::symbols::DispatchedRoot;
use super::{ByteSource, EncodedResult, EncodedValidationError};

const SOURCE_POLL_STRIDE: usize = 1_024;
const FINGERPRINT_SCHEMA: u32 = 1;
const ENTITY_KEY_HEADER_BYTES: usize = size_of::<Vec<u8>>();
const LOGICAL_DOMAIN: &[u8] = b"pyowl-core:snapshot-logical:v1\x00";
const DATATYPE_POLICY: &[u8] = b"datatype-policy:owl2-v1\x00";
const SIGNATURE_DOMAIN: &[u8] = b"pyowl-core:snapshot-signature:v1\x00";
const OVERLAY_STRUCTURAL_DOMAIN: &[u8] = b"pyowl-core:overlay-structural:v1\x00";
const COMPOSITE_STRUCTURAL_DOMAIN: &[u8] = b"pyowl-core:composite-structural:v1\x00";
const CONTEXT_DOMAIN: &[u8] = b"pyowl-core:view-structure-context:v1\x00";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralContextKind {
    Overlay,
    Composite,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralFingerprintMode {
    Effective,
    OverlayAnchorAlias,
}

impl StructuralContextKind {
    #[must_use]
    pub const fn encoded_name(self) -> &'static [u8] {
        match self {
            Self::Overlay => b"overlay",
            Self::Composite => b"composite",
        }
    }

    #[must_use]
    const fn structural_domain(self) -> &'static [u8] {
        match self {
            Self::Overlay => OVERLAY_STRUCTURAL_DOMAIN,
            Self::Composite => COMPOSITE_STRUCTURAL_DOMAIN,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralContextEvidence {
    pub kind: StructuralContextKind,
    pub canonical_bytes: Vec<u8>,
}

impl StructuralContextEvidence {
    pub fn new(kind: StructuralContextKind, canonical_bytes: Vec<u8>) -> EncodedResult<Self> {
        validate_context_bytes(kind, &canonical_bytes)?;
        Ok(Self {
            kind,
            canonical_bytes,
        })
    }

    fn overlay_anchor_digest(&self) -> EncodedResult<[u8; 32]> {
        if self.kind != StructuralContextKind::Overlay {
            return Err(EncodedValidationError::protocol(
                "overlay anchor digest requires an overlay structural context",
            ));
        }
        let mut cursor = CONTEXT_DOMAIN.len();
        let _kind = read_frame(
            &self.canonical_bytes,
            &mut cursor,
            "structural context kind",
        )?;
        let count = read_varint(
            &self.canonical_bytes,
            &mut cursor,
            "structural context fingerprint count",
        )?;
        if count != 1 {
            return Err(EncodedValidationError::protocol(
                "overlay structural context must contain one anchor fingerprint",
            ));
        }
        let fingerprint = read_frame(
            &self.canonical_bytes,
            &mut cursor,
            "structural context fingerprint",
        )?;
        let mut fingerprint_cursor = 0;
        let _algorithm = read_frame(
            fingerprint,
            &mut fingerprint_cursor,
            "structural context fingerprint algorithm",
        )?;
        let _schema = read_varint(
            fingerprint,
            &mut fingerprint_cursor,
            "structural context fingerprint schema",
        )?;
        let digest: [u8; 32] = fingerprint
            .get(fingerprint_cursor..)
            .and_then(|value| value.try_into().ok())
            .ok_or_else(|| {
                EncodedValidationError::protocol(
                    "overlay structural context anchor digest changed shape",
                )
            })?;
        Ok(digest)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ViewFingerprints {
    pub structural: [u8; 32],
    pub logical: [u8; 32],
    pub signature: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::struct_field_names)]
pub struct FingerprintPhaseLimits {
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_depth: usize,
    pub max_scope_maps: usize,
}

impl Default for FingerprintPhaseLimits {
    fn default() -> Self {
        Self {
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_depth: 512,
            max_scope_maps: 32,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum FingerprintPhaseError<E> {
    Encoded(EncodedValidationError),
    Control(E),
}

impl<E> From<EncodedValidationError> for FingerprintPhaseError<E> {
    fn from(error: EncodedValidationError) -> Self {
        Self::Encoded(error)
    }
}

type ControlledResult<T, E> = Result<T, FingerprintPhaseError<E>>;

#[derive(Debug)]
pub struct FingerprintContributions {
    annotations: Vec<Vec<u8>>,
    axioms: Vec<Vec<u8>>,
    extensions: Vec<Vec<u8>>,
    logical_axioms: Vec<Vec<u8>>,
    logical_extensions: Vec<Vec<u8>>,
    entity_keys: Vec<Vec<u8>>,
    work: u64,
    owned_bytes: usize,
}

impl FingerprintContributions {
    #[must_use]
    pub const fn work(&self) -> u64 {
        self.work
    }

    #[must_use]
    pub const fn owned_bytes(&self) -> usize {
        self.owned_bytes
    }
}

struct PhaseBudget<'a, E, F>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    limits: FingerprintPhaseLimits,
    work: u64,
    owned_bytes: usize,
    unpolled_work: usize,
    control: &'a mut F,
    control_error: Option<E>,
}

impl<'a, E, F> PhaseBudget<'a, E, F>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    const fn new(limits: FingerprintPhaseLimits, control: &'a mut F) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
            unpolled_work: 0,
            control,
            control_error: None,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount_u64 = u64::try_from(amount).map_err(|_| {
            EncodedValidationError::resource("fingerprint work exceeds the u64 accounting range")
        })?;
        self.work = self.work.checked_add(amount_u64).ok_or_else(|| {
            EncodedValidationError::resource("fingerprint work accounting overflowed")
        })?;
        if self.work > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "encoded fingerprint work exceeds its limit",
            ));
        }
        self.unpolled_work = self.unpolled_work.saturating_add(amount);
        if self.unpolled_work >= SOURCE_POLL_STRIDE {
            self.unpolled_work %= SOURCE_POLL_STRIDE;
            if let Err(error) = (self.control)("source-fingerprint-traversal") {
                self.control_error = Some(error);
                return Err(EncodedValidationError::invariant(
                    "fingerprint traversal was interrupted by its control callback",
                ));
            }
        }
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        self.owned_bytes = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("fingerprint ownership accounting overflowed")
        })?;
        if self.owned_bytes > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "encoded fingerprint ownership exceeds its limit",
            ));
        }
        Ok(())
    }

    fn poll(&mut self, phase: &'static str) -> ControlledResult<(), E> {
        (self.control)(phase).map_err(FingerprintPhaseError::Control)
    }

    fn controlled_work(&mut self, amount: usize) -> ControlledResult<(), E> {
        let result = self.claim_work(amount);
        self.map(result)
    }

    fn controlled_owned(&mut self, amount: usize) -> ControlledResult<(), E> {
        let result = self.claim_owned(amount);
        self.map(result)
    }

    fn map<T>(&mut self, result: EncodedResult<T>) -> ControlledResult<T, E> {
        match result {
            Ok(value) => Ok(value),
            Err(error) => match self.control_error.take() {
                Some(control_error) => Err(FingerprintPhaseError::Control(control_error)),
                None => Err(FingerprintPhaseError::Encoded(error)),
            },
        }
    }
}

impl<E, F> CanonicalBudget for PhaseBudget<'_, E, F>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    fn canonical_max_depth(&self) -> usize {
        self.limits.max_depth
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

/// Canonicalize every selected root in one bounded source transaction.
///
/// Logical axioms and extensions additionally emit their annotation-stripped
/// form in the same transaction; both traversals share the same work,
/// ownership, depth, and cancellation budget.
pub fn compile_fingerprint_contributions_controlled<B, E>(
    model: &ValidatedModel<B>,
    roots: &[DispatchedRoot],
    scope_maps: &[AnonymousScopeMap],
    limits: FingerprintPhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<FingerprintContributions, E>
where
    B: ByteSource,
{
    let mut budget = PhaseBudget::new(limits, control);
    budget.poll("source-fingerprint-preflight")?;
    let scope_validation = canonical::validate_scope_maps(scope_maps, &mut budget);
    budget.map(scope_validation)?;
    let mut annotations = Vec::new();
    let mut axioms = Vec::new();
    let mut extensions = Vec::new();
    let mut logical_axioms = Vec::new();
    let mut logical_extensions = Vec::new();
    let mut entity_keys = Vec::new();
    for root in roots {
        let canonical = canonical_node_key_with_entities(
            model,
            root.node,
            scope_maps,
            &mut entity_keys,
            &mut budget,
        );
        let canonical = budget.map(canonical)?;
        match root.kind {
            RootKind::OntologyAnnotation => {
                push_contribution(&mut annotations, canonical, &mut budget)?;
            }
            RootKind::Axiom => {
                if logical_axiom_tag(root.tag) {
                    let logical =
                        annotation_stripped_node_key(model, root.node, scope_maps, &mut budget);
                    let logical = budget.map(logical)?;
                    push_contribution(&mut logical_axioms, logical, &mut budget)?;
                }
                push_contribution(&mut axioms, canonical, &mut budget)?;
            }
            RootKind::Extension => {
                let logical =
                    annotation_stripped_node_key(model, root.node, scope_maps, &mut budget);
                let logical = budget.map(logical)?;
                push_contribution(&mut logical_extensions, logical, &mut budget)?;
                push_contribution(&mut extensions, canonical, &mut budget)?;
            }
        }
    }
    budget.poll("source-fingerprint-complete")?;
    Ok(FingerprintContributions {
        annotations,
        axioms,
        extensions,
        logical_axioms,
        logical_extensions,
        entity_keys,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
    })
}

/// Merge source contributions and hash the exact pyowl-core v1 preimages.
pub fn merge_view_fingerprints_controlled<E>(
    phases: Vec<FingerprintContributions>,
    context: &StructuralContextEvidence,
    structural_mode: StructuralFingerprintMode,
    limits: FingerprintPhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ViewFingerprints, E> {
    validate_context_bytes(context.kind, &context.canonical_bytes)?;
    if structural_mode == StructuralFingerprintMode::OverlayAnchorAlias
        && context.kind != StructuralContextKind::Overlay
    {
        return Err(FingerprintPhaseError::Encoded(
            EncodedValidationError::protocol(
                "overlay anchor structural alias requires an overlay context",
            ),
        ));
    }
    let mut budget = PhaseBudget::new(limits, control);
    budget.poll("merged-fingerprint-preflight")?;
    let prior_work = phases.iter().try_fold(0_u64, |total, phase| {
        total
            .checked_add(phase.work)
            .ok_or_else(|| EncodedValidationError::resource("source fingerprint work overflowed"))
    })?;
    let contribution_headers = phases
        .capacity()
        .checked_mul(size_of::<FingerprintContributions>())
        .ok_or_else(|| {
            EncodedValidationError::resource("source fingerprint contribution headers overflowed")
        })?;
    let prior_owned = phases
        .iter()
        .try_fold(contribution_headers, |total, phase| {
            total.checked_add(phase.owned_bytes).ok_or_else(|| {
                EncodedValidationError::resource("source fingerprint ownership overflowed")
            })
        })?;
    if prior_work > limits.max_work || prior_owned > limits.max_owned_bytes {
        return Err(FingerprintPhaseError::Encoded(
            EncodedValidationError::resource("source fingerprints exceed their aggregate limits"),
        ));
    }
    budget.work = prior_work;
    budget.owned_bytes = prior_owned;

    let mut annotations = Vec::new();
    let mut axioms = Vec::new();
    let mut extensions = Vec::new();
    let mut logical_axioms = Vec::new();
    let mut logical_extensions = Vec::new();
    let mut entity_keys = Vec::new();
    for mut phase in phases {
        append_owned(&mut annotations, &mut phase.annotations, &mut budget)?;
        append_owned(&mut axioms, &mut phase.axioms, &mut budget)?;
        append_owned(&mut extensions, &mut phase.extensions, &mut budget)?;
        append_owned(&mut logical_axioms, &mut phase.logical_axioms, &mut budget)?;
        append_owned(
            &mut logical_extensions,
            &mut phase.logical_extensions,
            &mut budget,
        )?;
        append_owned(&mut entity_keys, &mut phase.entity_keys, &mut budget)?;
    }
    canonicalize(&mut annotations, &mut budget)?;
    canonicalize(&mut axioms, &mut budget)?;
    canonicalize(&mut extensions, &mut budget)?;
    canonicalize(&mut logical_axioms, &mut budget)?;
    canonicalize(&mut logical_extensions, &mut budget)?;
    canonicalize(&mut entity_keys, &mut budget)?;
    budget.poll("merged-fingerprint-sort")?;

    let structural = match structural_mode {
        StructuralFingerprintMode::Effective => {
            let mut hasher = Sha256::new();
            update_bytes(&mut hasher, context.kind.structural_domain(), &mut budget)?;
            update_frame(&mut hasher, &context.canonical_bytes, &mut budget)?;
            update_collection(&mut hasher, &annotations, &mut budget)?;
            update_collection(&mut hasher, &axioms, &mut budget)?;
            update_collection(&mut hasher, &extensions, &mut budget)?;
            hasher.finalize().into()
        }
        StructuralFingerprintMode::OverlayAnchorAlias => context.overlay_anchor_digest()?,
    };
    let logical = {
        let mut hasher = Sha256::new();
        update_bytes(&mut hasher, LOGICAL_DOMAIN, &mut budget)?;
        update_bytes(&mut hasher, DATATYPE_POLICY, &mut budget)?;
        update_collection(&mut hasher, &logical_axioms, &mut budget)?;
        update_varint(&mut hasher, logical_extensions.len(), &mut budget)?;
        for value in &logical_extensions {
            update_bytes(&mut hasher, b"E", &mut budget)?;
            update_frame(&mut hasher, value, &mut budget)?;
        }
        hasher.finalize().into()
    };
    let signature = {
        let mut hasher = Sha256::new();
        update_bytes(&mut hasher, SIGNATURE_DOMAIN, &mut budget)?;
        // This flag records the core call contract. It does not inject entities
        // that are absent from the effective structural roots.
        update_bytes(&mut hasher, &[1_u8], &mut budget)?;
        update_collection(&mut hasher, &entity_keys, &mut budget)?;
        hasher.finalize().into()
    };
    budget.poll("merged-fingerprint-complete")?;
    Ok(ViewFingerprints {
        structural,
        logical,
        signature,
    })
}

fn append_owned<E, F>(
    target: &mut Vec<Vec<u8>>,
    source: &mut Vec<Vec<u8>>,
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    let old_capacity = target.capacity();
    target.try_reserve_exact(source.len()).map_err(|_| {
        FingerprintPhaseError::Encoded(EncodedValidationError::resource(
            "fingerprint contribution merge allocation failed",
        ))
    })?;
    let owned = target
        .capacity()
        .checked_sub(old_capacity)
        .and_then(|amount| amount.checked_mul(ENTITY_KEY_HEADER_BYTES))
        .ok_or_else(|| {
            EncodedValidationError::resource("fingerprint contribution merge size overflowed")
        })?;
    budget.controlled_owned(owned)?;
    target.append(source);
    Ok(())
}

fn push_contribution<E, F>(
    target: &mut Vec<Vec<u8>>,
    value: Vec<u8>,
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    let old_capacity = target.capacity();
    target.try_reserve_exact(1).map_err(|_| {
        FingerprintPhaseError::Encoded(EncodedValidationError::resource(
            "fingerprint contribution allocation failed",
        ))
    })?;
    let owned = target
        .capacity()
        .checked_sub(old_capacity)
        .and_then(|amount| amount.checked_mul(ENTITY_KEY_HEADER_BYTES))
        .ok_or_else(|| {
            EncodedValidationError::resource("fingerprint contribution size overflowed")
        })?;
    budget.controlled_owned(owned)?;
    target.push(value);
    Ok(())
}

fn canonicalize<E, F>(
    values: &mut Vec<Vec<u8>>,
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    let logarithm = if values.len() <= 1 {
        0
    } else {
        usize::BITS as usize - values.len().leading_zeros() as usize
    };
    let key_bytes = values.iter().try_fold(0_usize, |total, value| {
        total
            .checked_add(value.len())
            .ok_or_else(|| EncodedValidationError::resource("fingerprint key bytes overflowed"))
    })?;
    let sort_work = key_bytes
        .checked_mul(logarithm.max(1))
        .ok_or_else(|| EncodedValidationError::resource("fingerprint sort work overflowed"))?;
    let total_work = sort_work.checked_add(key_bytes).ok_or_else(|| {
        EncodedValidationError::resource("fingerprint deduplication work overflowed")
    })?;
    budget.controlled_work(total_work)?;
    values.sort_unstable();
    values.dedup();
    Ok(())
}

fn update_collection<E, F>(
    hasher: &mut Sha256,
    values: &[Vec<u8>],
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    update_varint(hasher, values.len(), budget)?;
    for value in values {
        update_frame(hasher, value, budget)?;
    }
    Ok(())
}

fn update_bytes<E, F>(
    hasher: &mut Sha256,
    value: &[u8],
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    budget.controlled_work(value.len())?;
    hasher.update(value);
    Ok(())
}

fn update_frame<E, F>(
    hasher: &mut Sha256,
    value: &[u8],
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    update_varint(hasher, value.len(), budget)?;
    update_bytes(hasher, value, budget)
}

fn update_varint<E, F>(
    hasher: &mut Sha256,
    value: usize,
    budget: &mut PhaseBudget<'_, E, F>,
) -> ControlledResult<(), E>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    let mut value = u64::try_from(value)
        .map_err(|_| EncodedValidationError::resource("fingerprint length exceeds u64"))?;
    loop {
        let payload = u8::try_from(value & 0x7f).map_err(|_| {
            EncodedValidationError::invariant("fingerprint varint payload exceeds u8")
        })?;
        value >>= 7;
        update_bytes(
            hasher,
            &[payload | if value == 0 { 0 } else { 0x80 }],
            budget,
        )?;
        if value == 0 {
            return Ok(());
        }
    }
}

const fn logical_axiom_tag(tag: u16) -> bool {
    matches!(
        tag,
        61..=64
            | 70..=82
            | 90..=95
            | 100..=101
            | 110..=116
    )
}

fn validate_context_bytes(expected_kind: StructuralContextKind, bytes: &[u8]) -> EncodedResult<()> {
    if bytes.len() > 128 * 1024 || !bytes.starts_with(CONTEXT_DOMAIN) {
        return Err(EncodedValidationError::protocol(
            "deferred structural context has an invalid domain or size",
        ));
    }
    let mut cursor = CONTEXT_DOMAIN.len();
    let kind = read_frame(bytes, &mut cursor, "structural context kind")?;
    if kind != expected_kind.encoded_name() {
        return Err(EncodedValidationError::protocol(
            "deferred structural context kind does not match its canonical bytes",
        ));
    }
    let count = read_varint(bytes, &mut cursor, "structural context fingerprint count")?;
    let valid_count = match expected_kind {
        StructuralContextKind::Overlay => count == 1,
        StructuralContextKind::Composite => (2..=1_024).contains(&count),
    };
    if !valid_count {
        return Err(EncodedValidationError::protocol(
            "deferred structural context has an invalid fingerprint count",
        ));
    }
    let count = usize::try_from(count).map_err(|_| {
        EncodedValidationError::resource(
            "deferred structural context fingerprint count exceeds usize",
        )
    })?;
    let mut previous: Option<&[u8]> = None;
    for _ in 0..count {
        let fingerprint = read_frame(bytes, &mut cursor, "structural context fingerprint")?;
        let mut fingerprint_cursor = 0;
        if read_frame(
            fingerprint,
            &mut fingerprint_cursor,
            "structural context fingerprint algorithm",
        )? != b"sha256"
            || read_varint(
                fingerprint,
                &mut fingerprint_cursor,
                "structural context fingerprint schema",
            )? != u64::from(FINGERPRINT_SCHEMA)
            || fingerprint.len().saturating_sub(fingerprint_cursor) != 32
        {
            return Err(EncodedValidationError::protocol(
                "deferred structural context fingerprint is not schema-1 SHA-256",
            ));
        }
        fingerprint_cursor += 32;
        if fingerprint_cursor != fingerprint.len() {
            return Err(EncodedValidationError::protocol(
                "deferred structural context fingerprint has trailing bytes",
            ));
        }
        if expected_kind == StructuralContextKind::Composite
            && previous.is_some_and(|value| value > fingerprint)
        {
            return Err(EncodedValidationError::protocol(
                "deferred composite structural context is not canonically ordered",
            ));
        }
        previous = Some(fingerprint);
    }
    if cursor != bytes.len() {
        return Err(EncodedValidationError::protocol(
            "deferred structural context has trailing bytes",
        ));
    }
    Ok(())
}

fn read_frame<'a>(
    bytes: &'a [u8],
    cursor: &mut usize,
    name: &'static str,
) -> EncodedResult<&'a [u8]> {
    let length = read_varint(bytes, cursor, name)?;
    let length = usize::try_from(length)
        .map_err(|_| EncodedValidationError::resource(format!("{name} exceeds usize")))?;
    let end = cursor
        .checked_add(length)
        .ok_or_else(|| EncodedValidationError::resource(format!("{name} end overflowed")))?;
    let value = bytes
        .get(*cursor..end)
        .ok_or_else(|| EncodedValidationError::protocol(format!("{name} is truncated")))?;
    *cursor = end;
    Ok(value)
}

fn read_varint(bytes: &[u8], cursor: &mut usize, name: &'static str) -> EncodedResult<u64> {
    let start = *cursor;
    let mut value = 0_u64;
    let mut shift = 0_u32;
    loop {
        let byte = *bytes
            .get(*cursor)
            .ok_or_else(|| EncodedValidationError::protocol(format!("{name} is truncated")))?;
        *cursor = cursor
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource(format!("{name} cursor overflowed")))?;
        if shift == 63 && byte > 1 {
            return Err(EncodedValidationError::protocol(format!(
                "{name} varint overflows u64"
            )));
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            let width = *cursor - start;
            if width > 1 && byte == 0 {
                return Err(EncodedValidationError::protocol(format!(
                    "{name} varint is noncanonical"
                )));
            }
            return Ok(value);
        }
        shift = shift
            .checked_add(7)
            .ok_or_else(|| EncodedValidationError::resource(format!("{name} shift overflowed")))?;
        if shift > 63 {
            return Err(EncodedValidationError::protocol(format!(
                "{name} varint is too wide"
            )));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(value: &[u8]) -> Vec<u8> {
        let mut encoded = Vec::new();
        let mut length = value.len() as u64;
        loop {
            let payload = (length & 0x7f) as u8;
            length >>= 7;
            encoded.push(payload | if length == 0 { 0 } else { 0x80 });
            if length == 0 {
                break;
            }
        }
        encoded.extend_from_slice(value);
        encoded
    }

    fn fingerprint(value: u8) -> Vec<u8> {
        let mut encoded = frame(b"sha256");
        encoded.push(1);
        encoded.extend_from_slice(&[value; 32]);
        encoded
    }

    fn context(kind: StructuralContextKind, values: &[u8]) -> Vec<u8> {
        let mut encoded = CONTEXT_DOMAIN.to_vec();
        encoded.extend(frame(kind.encoded_name()));
        encoded.push(values.len() as u8);
        for value in values {
            encoded.extend(frame(&fingerprint(*value)));
        }
        encoded
    }

    #[test]
    fn exact_context_validation_accepts_overlay_and_ordered_composite() {
        let overlay = context(StructuralContextKind::Overlay, &[7]);
        assert!(StructuralContextEvidence::new(StructuralContextKind::Overlay, overlay).is_ok());
        let composite = context(StructuralContextKind::Composite, &[1, 2, 2]);
        assert!(
            StructuralContextEvidence::new(StructuralContextKind::Composite, composite).is_ok()
        );
    }

    #[test]
    fn exact_context_validation_rejects_kind_order_and_trailing_bytes() {
        let overlay = context(StructuralContextKind::Overlay, &[7]);
        assert!(StructuralContextEvidence::new(StructuralContextKind::Composite, overlay).is_err());
        let unordered = context(StructuralContextKind::Composite, &[2, 1]);
        assert!(
            StructuralContextEvidence::new(StructuralContextKind::Composite, unordered).is_err()
        );
        let mut trailing = context(StructuralContextKind::Overlay, &[7]);
        trailing.push(0);
        assert!(StructuralContextEvidence::new(StructuralContextKind::Overlay, trailing).is_err());
    }

    #[test]
    fn merged_extension_and_signature_contributions_are_sorted_and_deduplicated(
    ) -> Result<(), String> {
        let context = StructuralContextEvidence::new(
            StructuralContextKind::Overlay,
            context(StructuralContextKind::Overlay, &[7]),
        )
        .map_err(|error| format!("valid context fixture was rejected: {error:?}"))?;
        let phases = vec![
            FingerprintContributions {
                annotations: Vec::new(),
                axioms: Vec::new(),
                extensions: vec![b"annotated-rule-b".to_vec(), b"annotated-rule-a".to_vec()],
                logical_axioms: Vec::new(),
                logical_extensions: vec![b"rule-b".to_vec(), b"rule-a".to_vec()],
                entity_keys: vec![b"entity-b".to_vec(), b"entity-a".to_vec()],
                work: 0,
                owned_bytes: 0,
            },
            FingerprintContributions {
                annotations: Vec::new(),
                axioms: Vec::new(),
                extensions: vec![b"annotated-rule-a".to_vec()],
                logical_axioms: Vec::new(),
                logical_extensions: vec![b"rule-a".to_vec()],
                entity_keys: vec![b"entity-a".to_vec()],
                work: 0,
                owned_bytes: 0,
            },
        ];
        let mut control = |_phase| Ok::<(), ()>(());
        let observed = merge_view_fingerprints_controlled(
            phases,
            &context,
            StructuralFingerprintMode::Effective,
            FingerprintPhaseLimits::default(),
            &mut control,
        )
        .map_err(|error| format!("merge fixture was rejected: {error:?}"))?;

        let mut structural = OVERLAY_STRUCTURAL_DOMAIN.to_vec();
        structural.extend(frame(&context.canonical_bytes));
        structural.push(0);
        structural.push(0);
        structural.push(2);
        for extension in [
            b"annotated-rule-a".as_slice(),
            b"annotated-rule-b".as_slice(),
        ] {
            structural.extend(frame(extension));
        }
        let mut logical = LOGICAL_DOMAIN.to_vec();
        logical.extend_from_slice(DATATYPE_POLICY);
        logical.push(0);
        logical.push(2);
        for extension in [b"rule-a".as_slice(), b"rule-b".as_slice()] {
            logical.push(b'E');
            logical.extend(frame(extension));
        }
        let mut signature = SIGNATURE_DOMAIN.to_vec();
        signature.push(1);
        signature.push(2);
        for entity in [b"entity-a".as_slice(), b"entity-b".as_slice()] {
            signature.extend(frame(entity));
        }

        let expected_structural: [u8; 32] = Sha256::digest(structural).into();
        let expected_logical: [u8; 32] = Sha256::digest(logical).into();
        let expected_signature: [u8; 32] = Sha256::digest(signature).into();
        assert_eq!(observed.structural, expected_structural);
        assert_eq!(observed.logical, expected_logical);
        assert_eq!(observed.signature, expected_signature);
        Ok(())
    }
}
