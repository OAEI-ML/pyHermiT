//! Bounded, namespace-isolated blocking signature cache.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;

use super::model::{BlockingControl, BlockingError, CoreBlockingMode, DirectCheckerKind};
use super::projection::BlockingSignature;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingCacheNamespace {
    pub ontology_fingerprint: String,
    pub vocabulary_fingerprint: String,
    pub checker_kind: DirectCheckerKind,
    pub core_mode: CoreBlockingMode,
    pub configuration_fingerprint: String,
}

impl BlockingCacheNamespace {
    pub fn new(
        ontology_fingerprint: impl Into<String>,
        vocabulary_fingerprint: impl Into<String>,
        checker_kind: DirectCheckerKind,
        core_mode: CoreBlockingMode,
        configuration_fingerprint: impl Into<String>,
    ) -> Result<Self, BlockingError> {
        let value = Self {
            ontology_fingerprint: ontology_fingerprint.into(),
            vocabulary_fingerprint: vocabulary_fingerprint.into(),
            checker_kind,
            core_mode,
            configuration_fingerprint: configuration_fingerprint.into(),
        };
        if value.ontology_fingerprint.is_empty()
            || value.vocabulary_fingerprint.is_empty()
            || value.configuration_fingerprint.is_empty()
        {
            return Err(BlockingError::invalid(
                "blocking cache fingerprints must be nonempty",
            ));
        }
        Ok(value)
    }

    #[must_use]
    pub fn key(&self) -> (&str, &str, &'static str, &'static str, &str) {
        (
            &self.ontology_fingerprint,
            &self.vocabulary_fingerprint,
            self.checker_kind.as_str(),
            self.core_mode.as_str(),
            &self.configuration_fingerprint,
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CachePromotionContext {
    pub satisfiable: bool,
    pub completed: bool,
    pub has_nominals: bool,
    pub has_additional_ontology: bool,
    pub query_local_axioms: bool,
    pub aborted: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CachePromotion {
    pub inserted: usize,
    pub entry_count: usize,
    pub size_bytes: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CacheEntry {
    signature: BlockingSignature,
    size_bytes: usize,
    last_used: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingSignatureCache {
    namespace: BlockingCacheNamespace,
    max_entries: usize,
    max_bytes: usize,
    size_bytes: usize,
    clock: u64,
    entries: BTreeMap<Vec<u8>, CacheEntry>,
}

impl BlockingSignatureCache {
    pub fn new(
        namespace: BlockingCacheNamespace,
        max_entries: usize,
        max_bytes: usize,
    ) -> Result<Self, BlockingError> {
        if max_entries == 0 || max_bytes == 0 {
            return Err(BlockingError::invalid(
                "blocking cache bounds must be strictly positive",
            ));
        }
        Ok(Self {
            namespace,
            max_entries,
            max_bytes,
            size_bytes: 0,
            clock: 0,
            entries: BTreeMap::new(),
        })
    }

    #[must_use]
    pub const fn namespace(&self) -> &BlockingCacheNamespace {
        &self.namespace
    }

    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub const fn size_bytes(&self) -> usize {
        self.size_bytes
    }

    #[must_use]
    pub const fn max_entries(&self) -> usize {
        self.max_entries
    }

    #[must_use]
    pub const fn max_bytes(&self) -> usize {
        self.max_bytes
    }

    pub fn contains(&mut self, signature: &BlockingSignature) -> Result<bool, BlockingError> {
        self.require_compatible(signature)?;
        let key = signature.canonical_bytes();
        let next = self.next_clock()?;
        let Some(entry) = self.entries.get_mut(&key) else {
            return Ok(false);
        };
        if entry.signature != *signature {
            return Err(BlockingError::invariant(
                "canonical blocking signature collision",
            ));
        }
        entry.last_used = next;
        Ok(true)
    }

    pub fn add(&mut self, signature: BlockingSignature) -> Result<bool, BlockingError> {
        self.require_compatible(&signature)?;
        let key = signature.canonical_bytes();
        let size_bytes = key.len().saturating_add(128);
        if size_bytes > self.max_bytes {
            return Ok(false);
        }
        let next = self.next_clock()?;
        if let Some(entry) = self.entries.get_mut(&key) {
            if entry.signature != signature {
                return Err(BlockingError::invariant(
                    "canonical blocking signature collision",
                ));
            }
            entry.last_used = next;
            return Ok(false);
        }
        self.entries.insert(
            key,
            CacheEntry {
                signature,
                size_bytes,
                last_used: next,
            },
        );
        self.size_bytes = self.size_bytes.saturating_add(size_bytes);
        self.evict();
        Ok(self.entries.values().any(|entry| entry.last_used == next))
    }

    pub fn promote_model<C: BlockingControl>(
        &mut self,
        signatures: impl IntoIterator<Item = BlockingSignature>,
        context: CachePromotionContext,
        control: &C,
    ) -> Result<CachePromotion, BlockingError> {
        if !context.satisfiable
            || !context.completed
            || context.has_nominals
            || context.has_additional_ontology
            || context.query_local_axioms
            || context.aborted
            || self.namespace.core_mode != CoreBlockingMode::None
        {
            return Ok(CachePromotion {
                inserted: 0,
                entry_count: self.entry_count(),
                size_bytes: self.size_bytes,
            });
        }
        let before = self.clone();
        let mut inserted = 0_usize;
        let outcome = (|| {
            for (index, signature) in signatures.into_iter().enumerate() {
                if index % 256 == 0 {
                    control.poll()?;
                }
                inserted = inserted.saturating_add(usize::from(self.add(signature)?));
                control.observe_memory(u64::try_from(self.size_bytes).unwrap_or(u64::MAX))?;
            }
            control.poll()?;
            Ok(CachePromotion {
                inserted,
                entry_count: self.entry_count(),
                size_bytes: self.size_bytes,
            })
        })();
        if outcome.is_err() {
            *self = before;
        }
        outcome
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.size_bytes = 0;
        self.clock = 0;
    }

    #[must_use]
    pub fn fingerprints(&self) -> Vec<String> {
        let mut values = self.entries.values().collect::<Vec<_>>();
        values.sort_by_key(|entry| entry.last_used);
        values
            .into_iter()
            .map(|entry| entry.signature.sha256())
            .collect()
    }

    fn require_compatible(&self, signature: &BlockingSignature) -> Result<(), BlockingError> {
        if signature.kind != self.namespace.checker_kind {
            return Err(BlockingError::invalid(
                "blocking signature checker kind does not match cache namespace",
            ));
        }
        Ok(())
    }

    fn next_clock(&mut self) -> Result<u64, BlockingError> {
        self.clock = self
            .clock
            .checked_add(1)
            .ok_or_else(|| BlockingError::invariant("blocking cache LRU clock overflow"))?;
        Ok(self.clock)
    }

    fn evict(&mut self) {
        while self.entries.len() > self.max_entries || self.size_bytes > self.max_bytes {
            let victim = self
                .entries
                .iter()
                .min_by_key(|(key, entry)| (entry.last_used, *key))
                .map(|(key, _entry)| key.clone());
            let Some(victim) = victim else {
                self.size_bytes = 0;
                return;
            };
            if let Some(entry) = self.entries.remove(&victim) {
                self.size_bytes = self.size_bytes.saturating_sub(entry.size_bytes);
            }
        }
    }
}
