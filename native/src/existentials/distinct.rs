//! Canonical bounded subset search used by object and data cardinalities.
// SPDX-License-Identifier: LGPL-3.0-or-later

use super::model::{ExpansionControl, ExpansionError, ExpansionLimits};

/// Search outcome exposed so Criterion can measure the primitive independently
/// of tableau allocation and assert that optimized/reference runs did the same
/// logical work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DistinctSearchResult {
    pub satisfied: bool,
    pub steps: u64,
    /// Lexicographically first successful subset in candidate order.
    pub selected_indices: Vec<usize>,
}

/// Find the lexicographically first pairwise-different subset with bounded,
/// iterative depth-first search.
///
/// Candidate order is semantic input: callers canonicalize representatives,
/// deduplicate them, and sort by stable creation rank first.  The iterative
/// implementation avoids recursion proportional to an ontology cardinality.
pub fn pairwise_distinct_subset<T, C, F>(
    candidates: &[T],
    cardinality: usize,
    limits: ExpansionLimits,
    control: &mut C,
    mut known_different: F,
) -> Result<DistinctSearchResult, ExpansionError>
where
    C: ExpansionControl,
    F: FnMut(&T, &T) -> Result<bool, ExpansionError>,
{
    control.poll()?;
    if cardinality == 0 {
        return Ok(DistinctSearchResult {
            satisfied: true,
            steps: 0,
            selected_indices: Vec::new(),
        });
    }
    if candidates.len() < cardinality {
        return Ok(DistinctSearchResult {
            satisfied: false,
            steps: 0,
            selected_indices: Vec::new(),
        });
    }
    if cardinality == 1 {
        return Ok(DistinctSearchResult {
            satisfied: true,
            steps: 0,
            selected_indices: vec![0],
        });
    }

    let mut selected = Vec::<usize>::new();
    let mut next_indices = vec![0_usize];
    let mut steps = 0_u64;

    while let Some(index) = next_indices.last().copied() {
        steps = steps
            .checked_add(1)
            .ok_or_else(|| ExpansionError::invariant("distinct-search step counter overflow"))?;
        if steps > limits.max_distinct_search_steps {
            return Err(ExpansionError::resource(
                "pairwise-distinct successor search limit exceeded",
                "max_distinct_search_steps",
                steps,
                limits.max_distinct_search_steps,
            ));
        }
        if steps % limits.cancellation_interval == 0 {
            control.add_work(limits.cancellation_interval)?;
            control.poll()?;
        }

        let still_needed = cardinality - selected.len();
        if index >= candidates.len() || candidates.len() - index < still_needed {
            next_indices.pop();
            selected.pop();
            continue;
        }
        if let Some(next) = next_indices.last_mut() {
            *next = index + 1;
        }
        let candidate = &candidates[index];
        let mut different = true;
        for selected_index in &selected {
            if !known_different(candidate, &candidates[*selected_index])? {
                different = false;
                break;
            }
        }
        if !different {
            continue;
        }
        selected.push(index);
        if selected.len() == cardinality {
            control.add_work(steps % limits.cancellation_interval)?;
            return Ok(DistinctSearchResult {
                satisfied: true,
                steps,
                selected_indices: selected,
            });
        }
        next_indices.push(index + 1);
    }

    control.add_work(steps % limits.cancellation_interval)?;
    Ok(DistinctSearchResult {
        satisfied: false,
        steps,
        selected_indices: Vec::new(),
    })
}
