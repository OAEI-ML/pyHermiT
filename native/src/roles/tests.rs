use super::*;
use serde::Deserialize;

fn limits() -> RoleLimits {
    RoleLimits {
        max_roles: 32,
        max_automata: 8,
        max_states: 64,
        max_transitions: 256,
        max_word_length: 32,
        max_memory_bytes: 1_000_000,
    }
}

fn transitive_wire() -> RoleAutomatonWire {
    // Epsilon shape intentionally mirrors the Python construction for R o R -> R:
    // initial -R-> final -epsilon-> initial.
    RoleAutomatonWire {
        component_id: 4,
        state_count: 2,
        initial_state: 0,
        final_states: vec![1],
        transitions: vec![
            RoleTransition::labelled(0, 2, 1),
            RoleTransition::epsilon(1, 0),
        ],
    }
}

fn runtime() -> Result<RoleRuntime, RoleError> {
    RoleRuntime::new(
        6,
        vec![0, 1, 3, 2, 4, 5],
        0,
        1,
        vec![transitive_wire()],
        limits(),
        &NeverCancel,
    )
}

#[test]
fn epsilon_nfa_streams_transitive_words() -> Result<(), RoleError> {
    let runtime = runtime()?;
    let automaton = runtime
        .automaton(4)
        .ok_or_else(|| RoleError::invalid("missing fixture automaton"))?;
    let mut cursor = automaton.cursor(&NeverCancel)?;
    assert_eq!(cursor.active_states(), vec![0]);
    assert!(automaton.advance(&mut cursor, 2, 6, &NeverCancel)?);
    assert_eq!(cursor.active_states(), vec![0, 1]);
    assert!(automaton.is_accepting(&cursor));
    assert!(automaton.advance(&mut cursor, 2, 6, &NeverCancel)?);
    assert!(automaton.is_accepting(&cursor));
    assert!(runtime.accepts(4, &[2], &NeverCancel)?);
    assert!(runtime.accepts(4, &[2, 2, 2], &NeverCancel)?);
    assert!(!runtime.accepts(4, &[], &NeverCancel)?);
    assert!(!runtime.accepts(4, &[3], &NeverCancel)?);
    Ok(())
}

#[test]
fn inverse_words_reverse_order_and_direction() -> Result<(), RoleError> {
    let runtime = runtime()?;
    assert_eq!(runtime.inverse_word(&[2, 4, 3])?, vec![2, 4, 3]);
    assert_eq!(runtime.inverse_word(&[2, 4])?, vec![4, 3]);
    assert_eq!(runtime.inverse_word(&[0, 1])?, vec![1, 0]);
    assert_eq!(
        runtime.inverse_word(&[6]).err().map(|error| error.kind),
        Some(RoleErrorKind::Invalid)
    );
    Ok(())
}

#[test]
fn top_bottom_hooks_do_not_materialize_relations() -> Result<(), RoleError> {
    let runtime = runtime()?;
    assert_eq!(
        runtime.builtin_semantics(0),
        Some(BuiltinRoleSemantics::Universal)
    );
    assert_eq!(
        runtime.builtin_semantics(1),
        Some(BuiltinRoleSemantics::Empty)
    );
    assert_eq!(
        runtime.builtin_semantics(2),
        Some(BuiltinRoleSemantics::Normal)
    );
    assert_eq!(runtime.builtin_semantics(99), None);
    assert!(runtime.accepts(4, &[2, 1, 3], &NeverCancel)?);
    assert_eq!(runtime.accepted_components(&[1], &NeverCancel)?, vec![4]);
    Ok(())
}

#[test]
fn decoding_canonicalizes_transition_order_and_duplicates() -> Result<(), RoleError> {
    let wire = RoleAutomatonWire {
        component_id: 9,
        state_count: 3,
        initial_state: 0,
        final_states: vec![2, 2],
        transitions: vec![
            RoleTransition::labelled(1, 2, 2),
            RoleTransition::epsilon(0, 1),
            RoleTransition::labelled(1, 2, 2),
        ],
    };
    let automaton = RoleAutomaton::from_wire(wire, 4, limits(), &NeverCancel)?;
    assert_eq!(automaton.transitions().len(), 2);
    assert!(automaton.accepts(&[2], 4, limits(), &NeverCancel)?);
    Ok(())
}

#[test]
fn cursors_cannot_cross_automaton_ownership_boundaries() -> Result<(), RoleError> {
    let first = RoleAutomaton::from_wire(transitive_wire(), 6, limits(), &NeverCancel)?;
    let second = RoleAutomaton::from_wire(
        RoleAutomatonWire {
            component_id: 5,
            ..transitive_wire()
        },
        6,
        limits(),
        &NeverCancel,
    )?;
    let mut cursor = first.cursor(&NeverCancel)?;
    assert_eq!(
        second
            .advance(&mut cursor, 2, 6, &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(RoleErrorKind::Invalid)
    );
    Ok(())
}

#[test]
fn hostile_bounds_fail_without_panics_or_partial_runtime() {
    let invalid_state = RoleAutomaton::from_wire(
        RoleAutomatonWire {
            component_id: 0,
            state_count: 1,
            initial_state: 1,
            final_states: vec![0],
            transitions: vec![],
        },
        1,
        limits(),
        &NeverCancel,
    );
    assert_eq!(
        invalid_state.err().map(|error| error.kind),
        Some(RoleErrorKind::Invalid)
    );

    let mut tiny = limits();
    tiny.max_states = 1;
    let oversized = RoleAutomaton::from_wire(transitive_wire(), 6, tiny, &NeverCancel);
    assert_eq!(
        oversized.err().map(|error| error.kind),
        Some(RoleErrorKind::Resource)
    );

    let invalid_inverse = RoleRuntime::new(2, vec![1, 1], 0, 1, vec![], limits(), &NeverCancel);
    assert_eq!(
        invalid_inverse.err().map(|error| error.kind),
        Some(RoleErrorKind::Invalid)
    );
}

#[derive(Debug)]
struct CancelAfter {
    polls: std::cell::Cell<usize>,
    allowed: usize,
}

impl RoleControl for CancelAfter {
    fn poll(&self) -> Result<(), RoleError> {
        let polls = self.polls.get();
        self.polls.set(polls.saturating_add(1));
        if polls >= self.allowed {
            return Err(RoleError::cancelled("test cancellation"));
        }
        Ok(())
    }
}

#[test]
fn construction_and_execution_are_cooperatively_cancellable() -> Result<(), RoleError> {
    let control = CancelAfter {
        polls: std::cell::Cell::new(0),
        allowed: 0,
    };
    let result = RoleAutomaton::from_wire(transitive_wire(), 6, limits(), &control);
    assert_eq!(
        result.err().map(|error| error.kind),
        Some(RoleErrorKind::Cancelled)
    );

    let runtime = runtime()?;
    let control = CancelAfter {
        polls: std::cell::Cell::new(0),
        allowed: 0,
    };
    assert_eq!(
        runtime
            .accepts(4, &[2], &control)
            .err()
            .map(|error| error.kind),
        Some(RoleErrorKind::Cancelled)
    );
    Ok(())
}

#[derive(Debug, Deserialize)]
struct DifferentialFixture {
    schema_version: u32,
    role_count: u32,
    inverse_role_ids: Vec<u32>,
    top_role_id: u32,
    bottom_role_id: u32,
    word_count_per_automaton: usize,
    automata: Vec<RoleAutomatonWire>,
    cases: Vec<DifferentialCase>,
}

#[derive(Debug, Deserialize)]
struct DifferentialCase {
    component_id: u32,
    word: Vec<u32>,
    accepts: bool,
}

#[test]
fn bounded_words_match_the_shared_python_nfa_fixture() -> Result<(), Box<dyn std::error::Error>> {
    let fixture: DifferentialFixture = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tests/data/roles/wpr3-role-automata-v1.json"
    )))?;
    assert_eq!(fixture.schema_version, 1);
    assert_eq!(
        fixture.cases.len(),
        fixture.word_count_per_automaton * fixture.automata.len()
    );
    let runtime = RoleRuntime::new(
        fixture.role_count,
        fixture.inverse_role_ids,
        fixture.top_role_id,
        fixture.bottom_role_id,
        fixture.automata,
        RoleLimits::default(),
        &NeverCancel,
    )?;
    for case in fixture.cases {
        let automaton = runtime
            .automaton(case.component_id)
            .ok_or_else(|| RoleError::invalid("fixture references an absent component"))?;
        assert_eq!(
            automaton.accepts(
                &case.word,
                fixture.role_count,
                RoleLimits::default(),
                &NeverCancel,
            )?,
            case.accepts,
            "component={} word={:?}",
            case.component_id,
            case.word,
        );
    }
    Ok(())
}
