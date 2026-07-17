//! Safe Rust tableau state kernel and language-neutral trace replay.
// SPDX-License-Identifier: LGPL-3.0-or-later

mod state;
mod trace;

pub use state::TableauKernel;
pub use trace::{replay_state_trace, STATE_TRACE_MAGIC, STATE_TRACE_VERSION};
