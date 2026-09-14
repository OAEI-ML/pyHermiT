//! Native-issued service results retain validated caches and their session identity.
// SPDX-License-Identifier: LGPL-3.0-or-later

use crate::error::{NativeError, NativeResult};
use crate::services::{ClassificationDomain, HierarchyIds, RealizationIds};
use crate::{NativeServiceSymbols, SessionControl};
use pyo3::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[pyclass(module = "pyhermit._native", name = "_NativeHierarchyResult", frozen)]
pub(crate) struct NativeHierarchyResult {
    pub(crate) control: Arc<SessionControl>,
    pub(crate) value: Arc<HierarchyIds>,
    pub(crate) domain: ClassificationDomain,
    member_nodes: BTreeMap<u32, u32>,
    parents: Vec<Vec<u32>>,
    children: Vec<Vec<u32>>,
}

type HierarchyRows = (Vec<Vec<u32>>, Vec<(u32, u32)>, u32, u32);
type RealizationRows = (
    Vec<Vec<u32>>,
    Vec<(u32, Vec<u32>)>,
    Vec<(u32, u32, Vec<u32>)>,
    Vec<(u32, u32, Vec<u32>)>,
    Vec<(u32, u32)>,
);

impl NativeHierarchyResult {
    pub(crate) fn new(
        control: Arc<SessionControl>,
        value: Arc<HierarchyIds>,
        domain: ClassificationDomain,
    ) -> NativeResult<Self> {
        let members = value.nodes.iter().map(Vec::len).sum::<usize>();
        let bytes = members
            .checked_mul(64)
            .and_then(|n| {
                value
                    .nodes
                    .len()
                    .checked_mul(64)
                    .and_then(|m| n.checked_add(m))
            })
            .and_then(|n| {
                value
                    .edges
                    .len()
                    .checked_mul(24)
                    .and_then(|m| n.checked_add(m))
            })
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| NativeError::wire("native hierarchy index size overflow"))?;
        control.cancellation.observe_memory(bytes);
        control.cancellation.poll()?;
        let mut member_nodes = BTreeMap::new();
        let mut parents = vec![Vec::new(); value.nodes.len()];
        let mut children = vec![Vec::new(); value.nodes.len()];
        for (node, identifiers) in value.nodes.iter().enumerate() {
            control.cancellation.poll()?;
            let node =
                u32::try_from(node).map_err(|_| NativeError::wire("hierarchy node overflow"))?;
            for identifier in identifiers {
                member_nodes.insert(*identifier, node);
            }
        }
        for (child, parent) in &value.edges {
            control.cancellation.poll()?;
            let c = usize::try_from(*child)
                .map_err(|_| NativeError::wire("hierarchy child overflow"))?;
            let p = usize::try_from(*parent)
                .map_err(|_| NativeError::wire("hierarchy parent overflow"))?;
            parents[c].push(*parent);
            children[p].push(*child);
        }
        Ok(Self {
            control,
            value,
            domain,
            member_nodes,
            parents,
            children,
        })
    }
}

#[pymethods]
impl NativeHierarchyResult {
    fn member_node(&self, py: Python<'_>, member: u32) -> PyResult<Option<u32>> {
        self.control
            .run(|_| Ok(self.member_nodes.get(&member).copied()))
            .map_err(|error| error.into_pyerr(py))
    }

    fn related(
        &self,
        py: Python<'_>,
        node: usize,
        upward: bool,
        direct: bool,
    ) -> PyResult<Vec<u32>> {
        self.control
            .run(|_| {
                py.detach(|| {
                    let adjacent = if upward {
                        &self.parents
                    } else {
                        &self.children
                    };
                    let initial = adjacent
                        .get(node)
                        .ok_or_else(|| NativeError::wire("hierarchy node out of range"))?;
                    if direct {
                        return Ok(initial.clone());
                    }
                    let mut reached = BTreeSet::new();
                    let mut pending = initial.clone();
                    while let Some(current) = pending.pop() {
                        self.control.cancellation.poll()?;
                        if reached.insert(current) {
                            let index = usize::try_from(current)
                                .map_err(|_| NativeError::wire("hierarchy node overflow"))?;
                            pending.extend_from_slice(&adjacent[index]);
                        }
                    }
                    Ok(reached.into_iter().collect())
                })
            })
            .map_err(|error| error.into_pyerr(py))
    }

    fn reaches(&self, py: Python<'_>, child: usize, parent: u32) -> PyResult<bool> {
        self.control
            .run(|_| {
                py.detach(|| {
                    if child >= self.parents.len()
                        || usize::try_from(parent).map_or(true, |n| n >= self.parents.len())
                    {
                        return Err(NativeError::wire("hierarchy node out of range"));
                    }
                    if u32::try_from(child).ok() == Some(parent) {
                        return Ok(true);
                    }
                    let mut visited = BTreeSet::new();
                    let mut pending = self.parents[child].clone();
                    while let Some(node) = pending.pop() {
                        self.control.cancellation.poll()?;
                        if node == parent {
                            return Ok(true);
                        }
                        if visited.insert(node) {
                            let index = usize::try_from(node)
                                .map_err(|_| NativeError::wire("hierarchy node overflow"))?;
                            pending.extend_from_slice(&self.parents[index]);
                        }
                    }
                    Ok(false)
                })
            })
            .map_err(|error| error.into_pyerr(py))
    }

    fn rows(&self, py: Python<'_>) -> PyResult<HierarchyRows> {
        // Materialize only the requested public result, never a permanent program.
        self.control
            .run(|_| {
                Ok((
                    self.value.nodes.clone(),
                    self.value.edges.clone(),
                    self.value.top_node,
                    self.value.bottom_node,
                ))
            })
            .map_err(|error| error.into_pyerr(py))
    }

    fn matches(
        &self,
        py: Python<'_>,
        symbols: &NativeServiceSymbols,
        domain: &str,
    ) -> PyResult<bool> {
        let expected = match self.domain {
            ClassificationDomain::Classes => "class",
            ClassificationDomain::ObjectProperties => "object_property",
            ClassificationDomain::DataProperties => "data_property",
        };
        self.control
            .run(|_| Ok(domain == expected && Arc::ptr_eq(&self.control, &symbols.control)))
            .map_err(|error| error.into_pyerr(py))
    }
}

#[pyclass(module = "pyhermit._native", name = "_NativeRealizationResult", frozen)]
pub(crate) struct NativeRealizationResult {
    pub(crate) control: Arc<SessionControl>,
    pub(crate) value: Arc<RealizationIds>,
}

#[pymethods]
impl NativeRealizationResult {
    fn rows(&self, py: Python<'_>) -> PyResult<RealizationRows> {
        self.control
            .run(|_| {
                Ok((
                    self.value.same_as().to_vec(),
                    self.value.direct_types().to_vec(),
                    self.value.object_targets().to_vec(),
                    self.value.data_targets().to_vec(),
                    self.value.different_from().to_vec(),
                ))
            })
            .map_err(|error| error.into_pyerr(py))
    }

    fn matches(
        &self,
        py: Python<'_>,
        symbols: &NativeServiceSymbols,
        domain: &str,
    ) -> PyResult<bool> {
        self.control
            .run(|_| Ok(domain == "individual" && Arc::ptr_eq(&self.control, &symbols.control)))
            .map_err(|error| error.into_pyerr(py))
    }

    fn matches_hierarchy(
        &self,
        py: Python<'_>,
        hierarchy: &NativeHierarchyResult,
    ) -> PyResult<bool> {
        self.control
            .run(|_| {
                Ok(hierarchy.domain == ClassificationDomain::Classes
                    && Arc::ptr_eq(&self.control, &hierarchy.control))
            })
            .map_err(|error| error.into_pyerr(py))
    }
}
