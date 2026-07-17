"""Pure-Python Hyp-rule execution and exhaustive ground-head dispatch.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import replace

from pyhermit.backends.python.branching import DisjunctionBrancher
from pyhermit.backends.python.state import (
    BranchingPoint,
    Clash,
    ClashKind,
    DependencySet,
    FactRow,
    NodeHandle,
    NodeSort,
    TableauSession,
)
from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DataConstant,
    GroundAtom,
    IndividualTerm,
    Predicate,
    PredicateKind,
    TermSort,
    Variable,
)
from pyhermit.clauses.model import GroundTerm
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError

from .joins import IndexedJoinEvaluator, NaiveJoinEvaluator
from .model import (
    BranchTransition,
    GroundRuleAtom,
    JoinMatch,
    PendingAnnotatedEquality,
    RuleLimits,
)
from .plans import ClauseJoinPlan, JoinProgram, compile_join_program

_NEGATION_PAIRS = (
    (PredicateKind.CONCEPT, PredicateKind.NEGATED_CONCEPT),
    (PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL),
    (PredicateKind.OBJECT_ROLE, PredicateKind.NEGATED_OBJECT_ROLE),
    (PredicateKind.DATA_ROLE, PredicateKind.NEGATED_DATA_ROLE),
    (PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE),
)


class HyperresolutionEngine:
    """Own query-local rule caches while borrowing immutable IR and mutable state."""

    __slots__ = (
        "_atom_by_id",
        "_atom_ids",
        "_brancher",
        "_data_identities_by_handle",
        "_data_nodes",
        "_disjunction_keys",
        "_equality_by_sort",
        "_inequality_by_sort",
        "_initialized",
        "_join_program",
        "_limits",
        "_opposites",
        "_pending_annotated",
        "_pending_by_atom",
        "_plans_by_predicate",
        "_program",
        "_session",
        "_source_nodes",
    )

    def __init__(
        self,
        program: ClauseProgram,
        session: TableauSession,
        *,
        source_nodes: Mapping[int, NodeHandle],
        data_nodes: Mapping[int, NodeHandle],
        limits: RuleLimits | None = None,
        disjunction_learning: bool = True,
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        selected_limits = RuleLimits() if limits is None else limits
        if not isinstance(selected_limits, RuleLimits):
            raise TypeError("limits must be RuleLimits or None")
        if not isinstance(disjunction_learning, bool):
            raise TypeError("disjunction_learning must be bool")
        self._program = program
        self._session = session
        self._source_nodes = _node_map(source_nodes, "source_nodes")
        self._data_nodes = _node_map(data_nodes, "data_nodes")
        identities_by_handle: dict[NodeHandle, set[int]] = {}
        for identity, handle in self._data_nodes.items():
            identities_by_handle.setdefault(handle, set()).add(identity)
        self._data_identities_by_handle = {
            handle: frozenset(identities) for handle, identities in identities_by_handle.items()
        }
        self._limits = selected_limits
        self._join_program = compile_join_program(program)
        grouped: dict[int, list[ClauseJoinPlan]] = {}
        for plan in self._join_program.plans:
            predicate_id = program.clauses[plan.clause_id].body[plan.delta_body_index].predicate_id
            grouped.setdefault(predicate_id, []).append(plan)
        self._plans_by_predicate = {
            key: tuple(sorted(values, key=lambda value: (value.clause_id, value.delta_body_index)))
            for key, values in grouped.items()
        }
        self._opposites = _opposite_predicates(program)
        self._equality_by_sort = _predicates_by_sort(program, PredicateKind.EQUALITY)
        self._inequality_by_sort = _predicates_by_sort(program, PredicateKind.INEQUALITY)
        self._atom_ids: dict[GroundRuleAtom, int] = {}
        self._atom_by_id: dict[int, GroundRuleAtom] = {}
        self._disjunction_keys: dict[tuple[int, ...], int] = {}
        self._pending_annotated: dict[int, PendingAnnotatedEquality] = {}
        self._pending_by_atom: dict[GroundRuleAtom, int] = {}
        self._initialized = False
        self._brancher = DisjunctionBrancher(
            session,
            self,
            learning=disjunction_learning,
        )

    @property
    def program(self) -> ClauseProgram:
        return self._program

    @property
    def session(self) -> TableauSession:
        return self._session

    @property
    def join_program(self) -> JoinProgram:
        return self._join_program

    @property
    def brancher(self) -> DisjunctionBrancher:
        return self._brancher

    @property
    def initialized(self) -> bool:
        return self._initialized

    def initialize(self, token: CancellationToken) -> None:
        """Install compiled ground input and unconditional rules at an operation root."""

        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        if self._initialized:
            raise ValueError("hyperresolution engine is already initialized")
        self._session.begin_operation()

        def operation() -> None:
            self._seed_reflexive_equalities()
            for fact in self._program.positive_facts + self._program.negative_facts:
                atom, dependency = self._ground_compiled_atom(fact)
                self.dispatch_ground_atom(
                    atom,
                    dependency,
                    provenance_ids=fact.provenance_ids,
                )
            for disjunction in self._program.ground_disjunctions:
                atoms_and_dependencies = tuple(
                    self._ground_compiled_atom(value) for value in disjunction.disjuncts
                )
                dependency = self._session.dependencies.union(
                    *(value[1] for value in atoms_and_dependencies)
                )
                self._apply_ground_head(
                    tuple(value[0] for value in atoms_and_dependencies),
                    dependency,
                    provenance_ids=disjunction.provenance_ids,
                    participant_ids=(disjunction.disjunction_id,),
                )
            self._fire_unconditional(token)
            self._session.check_invariants()

        self._session.run_with_recovery(token, operation)
        self._session.begin_operation()
        self._initialized = True

    def apply_next_delta(self, token: CancellationToken) -> int:
        """Advance one immutable delta generation and apply every triggered join plan."""

        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        if not self._initialized:
            raise ValueError("hyperresolution engine must be initialized first")
        return self._session.run_with_recovery(token, lambda: self._apply_next_delta(token))

    def _apply_next_delta(self, token: CancellationToken) -> int:
        token.check()
        self._session.extensions.prepare_next_delta()
        generation = self._session.extensions.read_generation
        rows = tuple(
            row
            for row in self._session.extensions.active_rows()
            if row.derivation_generation == generation
        )
        evaluator = self._indexed_evaluator(token)
        applied: set[tuple[int, tuple[object, ...], int]] = set()
        match_count = 0
        for row in rows:
            token.check()
            if not row.active:
                continue
            for plan in self._plans_by_predicate.get(row.key.predicate_id, ()):
                if not row.active or self._session.clashes.current is not None:
                    break
                for match in evaluator.matches(plan, row):
                    key = (
                        match.clause_id,
                        tuple(
                            (
                                value.sort.value,
                                value.variable_id,
                                value.node.slot,
                                value.node.generation,
                            )
                            for value in match.bindings
                        ),
                        match.dependency.bits,
                    )
                    if key in applied:
                        continue
                    applied.add(key)
                    match_count += 1
                    if match_count > self._limits.max_matches_per_generation:
                        raise ResourceLimitError(
                            "hyperresolution match limit exceeded",
                            limit="max_matches_per_generation",
                            observed=match_count,
                            allowed=self._limits.max_matches_per_generation,
                        )
                    self._apply_match(match)
                    if self._has_clash():
                        break
        token.add_work(evaluator.steps % self._limits.cancellation_interval)
        token.check()
        return len(rows)

    def saturate_hyperresolution(self, token: CancellationToken) -> int:
        generations = 0
        while self._session.clashes.current is None:
            processed = self.apply_next_delta(token)
            if processed == 0:
                return generations
            generations += 1
        return generations

    def indexed_matches(
        self,
        plan: ClauseJoinPlan,
        delta_row: FactRow,
        token: CancellationToken,
    ) -> tuple[JoinMatch, ...]:
        return self._indexed_evaluator(token).matches(plan, delta_row)

    def naive_matches(
        self,
        clause_id: int,
        token: CancellationToken,
        *,
        require_new: bool = True,
    ) -> tuple[JoinMatch, ...]:
        return NaiveJoinEvaluator(self._indexed_evaluator(token)).matches(
            clause_id,
            require_new=require_new,
        )

    def dispatch_ground_atom(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        *,
        provenance_ids: tuple[int, ...] = (),
    ) -> bool:
        if not isinstance(atom, GroundRuleAtom):
            raise TypeError("atom must be GroundRuleAtom")
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        predicate = self._program.predicates.predicate(atom.predicate_id)
        normalized, path = self._canonical_atom(atom)
        support = self._session.dependencies.union(dependency, path)
        self._validate_ground_sorts(predicate, normalized.arguments)
        if predicate.kind is PredicateKind.ORDERING_GUARD:
            raise InternalInvariantError("ordering guards cannot be dispatched as heads")
        if predicate.kind is PredicateKind.EQUALITY:
            return self._dispatch_equality(normalized, support, provenance_ids)
        if predicate.kind is PredicateKind.ANNOTATED_EQUALITY:
            return self._dispatch_annotated_equality(normalized, support, provenance_ids)
        changed = self._add_extension_atom(normalized, support, provenance_ids)
        if predicate.kind is PredicateKind.INEQUALITY and (
            normalized.arguments[0] == normalized.arguments[1]
        ):
            self._session.install_clash(
                Clash(
                    ClashKind.EQUALITY_INEQUALITY,
                    support,
                    (self.atom_id(normalized),),
                )
            )
        opposite = self._opposites.get(predicate.predicate_id)
        if opposite is not None:
            refutation = self._fact_dependency(opposite, normalized.arguments)
            if refutation is not None:
                self._session.install_clash(
                    Clash(
                        ClashKind.POSITIVE_NEGATIVE_ATOM,
                        self._session.dependencies.union(support, refutation),
                        (self.atom_id(normalized),),
                    )
                )
            elif predicate.kind in {
                PredicateKind.DATA_ROLE,
                PredicateKind.NEGATED_DATA_ROLE,
            }:
                self._derive_concrete_role_inequalities(
                    normalized,
                    opposite,
                    support,
                    provenance_ids,
                )
        if predicate.kind in {PredicateKind.AT_LEAST_OBJECT, PredicateKind.AT_LEAST_DATA}:
            root = normalized.arguments[0]
            self._session.nodes.mark_existential(root, predicate.predicate_id, pending=True)
            node = self._session.nodes.get(root)
            self._session.existential_candidates.enqueue(
                root,
                (node.creation_id, root.slot, root.generation),
            )
        return changed

    def apply_ground_head(
        self,
        atoms: tuple[GroundRuleAtom, ...],
        dependency: DependencySet,
        *,
        provenance_ids: tuple[int, ...] = (),
        participant_ids: tuple[int, ...] = (),
    ) -> bool:
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        if not all(isinstance(value, GroundRuleAtom) for value in atoms):
            raise TypeError("head atoms must be GroundRuleAtom values")
        return self._apply_ground_head(
            tuple(atoms),
            dependency,
            provenance_ids=provenance_ids,
            participant_ids=participant_ids,
        )

    def atom_id(self, atom: GroundRuleAtom) -> int:
        known = self._atom_ids.get(atom)
        if known is not None:
            return known
        encoded = json.dumps(
            {
                "arguments": [[value.slot, value.generation] for value in atom.arguments],
                "predicate_id": atom.predicate_id,
            },
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
        identifier = int.from_bytes(hashlib.sha256(encoded).digest(), "big")
        collision = self._atom_by_id.get(identifier)
        if collision is not None and collision != atom:
            raise InternalInvariantError("ground-atom SHA-256 identifier collision")
        self._atom_ids[atom] = identifier
        self._atom_by_id[identifier] = atom
        return identifier

    def atom_for_id(self, atom_id: int) -> GroundRuleAtom:
        try:
            return self._atom_by_id[atom_id]
        except KeyError as error:
            raise InternalInvariantError("ground disjunction references an absent atom") from error

    def atom_is_satisfied(self, atom: GroundRuleAtom) -> bool:
        predicate = self._program.predicates.predicate(atom.predicate_id)
        normalized, _path = self._canonical_atom(atom)
        if predicate.kind is PredicateKind.EQUALITY:
            return normalized.arguments[0] == normalized.arguments[1]
        if predicate.kind is PredicateKind.INEQUALITY and self._fixed_data_values_differ(
            normalized.arguments
        ):
            return True
        if predicate.kind is PredicateKind.ANNOTATED_EQUALITY:
            return normalized in self._pending_by_atom
        return self._fact_dependency(normalized.predicate_id, normalized.arguments) is not None

    def atom_refutation_dependency(self, atom: GroundRuleAtom) -> DependencySet | None:
        predicate = self._program.predicates.predicate(atom.predicate_id)
        normalized, path = self._canonical_atom(atom)
        if predicate.kind is PredicateKind.EQUALITY:
            if self._fixed_data_values_differ(normalized.arguments):
                return path
            inequality = self._inequality_by_sort.get(predicate.argument_sorts[0])
            found = (
                None
                if inequality is None
                else self._fact_dependency(inequality, normalized.arguments)
            )
            return None if found is None else self._session.dependencies.union(path, found)
        if predicate.kind is PredicateKind.INEQUALITY:
            if normalized.arguments[0] == normalized.arguments[1]:
                return path
            equality = self._equality_by_sort.get(predicate.argument_sorts[0])
            found = (
                None if equality is None else self._fact_dependency(equality, normalized.arguments)
            )
            return None if found is None else self._session.dependencies.union(path, found)
        opposite = self._opposites.get(predicate.predicate_id)
        if opposite is None:
            return None
        found = self._fact_dependency(opposite, normalized.arguments)
        return None if found is None else self._session.dependencies.union(path, found)

    def pending_annotated_equality(self, action_id: int) -> PendingAnnotatedEquality:
        try:
            return self._pending_annotated[action_id]
        except KeyError as error:
            raise KeyError(action_id) from error

    def take_pending_annotated_equality(self) -> PendingAnnotatedEquality | None:
        action_id = self._session.annotated_equalities.pop(
            lambda value: value in self._pending_annotated
        )
        return None if action_id is None else self._pending_annotated[action_id]

    def process_next_disjunction(self, token: CancellationToken) -> BranchTransition:
        return self._brancher.process_next(token)

    def resolve_clash(self, token: CancellationToken) -> BranchTransition:
        return self._brancher.resolve_until_choice_or_unsat(token)

    def _indexed_evaluator(self, token: CancellationToken) -> IndexedJoinEvaluator:
        return IndexedJoinEvaluator(
            self._program,
            self._session,
            source_nodes=self._source_nodes,
            data_nodes=self._data_nodes,
            token=token,
            limits=self._limits,
        )

    def _apply_match(self, match: JoinMatch) -> bool:
        clause = self._program.clauses[match.clause_id]
        bindings = {(value.sort, value.variable_id): value.node for value in match.bindings}
        atoms: list[GroundRuleAtom] = []
        dependencies = [match.dependency]
        for atom in clause.head:
            grounded, path = self._ground_atom(atom, bindings)
            atoms.append(grounded)
            dependencies.append(path)
        return self._apply_ground_head(
            tuple(atoms),
            self._session.dependencies.union(*dependencies),
            provenance_ids=clause.provenance_ids,
            participant_ids=match.premise_row_ids,
        )

    def _apply_ground_head(
        self,
        atoms: tuple[GroundRuleAtom, ...],
        dependency: DependencySet,
        *,
        provenance_ids: tuple[int, ...],
        participant_ids: tuple[int, ...],
    ) -> bool:
        canonicalized = tuple(self._canonical_atom(value) for value in atoms)
        normalized = tuple(dict.fromkeys(value[0] for value in canonicalized))
        if any(self.atom_is_satisfied(value) for value in normalized):
            return False
        remaining: list[GroundRuleAtom] = []
        dependencies = [dependency, *(value[1] for value in canonicalized)]
        for atom in normalized:
            refutation = self.atom_refutation_dependency(atom)
            if refutation is None:
                remaining.append(atom)
            else:
                dependencies.append(refutation)
        support = self._session.dependencies.union(*dependencies)
        if not remaining:
            clash_kind = ClashKind.EMPTY_HEAD
            if len(normalized) == 1:
                predicate_kind = self._program.predicates.predicate(normalized[0].predicate_id).kind
                if predicate_kind in {PredicateKind.EQUALITY, PredicateKind.INEQUALITY}:
                    clash_kind = ClashKind.EQUALITY_INEQUALITY
                elif normalized[0].predicate_id in self._opposites:
                    clash_kind = ClashKind.POSITIVE_NEGATIVE_ATOM
            return self._session.install_clash(
                Clash(
                    clash_kind,
                    support,
                    tuple(sorted(set(participant_ids))),
                    None if not provenance_ids else provenance_ids[0],
                )
            )
        if len(remaining) == 1:
            return self.dispatch_ground_atom(
                remaining[0],
                support,
                provenance_ids=provenance_ids,
            )
        return self._install_disjunction(tuple(remaining), support)

    def _install_disjunction(
        self,
        atoms: tuple[GroundRuleAtom, ...],
        dependency: DependencySet,
    ) -> bool:
        ordered = tuple(sorted(set(atoms), key=self._disjunct_rank))
        identifiers = tuple(self.atom_id(value) for value in ordered)
        known = self._disjunction_keys.get(identifiers)
        if known is not None:
            try:
                record = self._session.disjunctions.get(known)
            except KeyError:
                self._disjunction_keys.pop(identifiers, None)
            else:
                if record.active and _dependency_rank(dependency) < _dependency_rank(
                    record.base_dependency
                ):
                    previous = record.base_dependency
                    self._session.trail.record(
                        "rules.disjunction.support",
                        lambda: setattr(record, "base_dependency", previous),
                    )
                    record.base_dependency = self._session.dependencies.intern(dependency)
                    for branch in self._session.branches:
                        if branch.source_id == known:
                            old_base = branch.base_dependency

                            def undo_branch_support(
                                branch: BranchingPoint = branch,
                                old_base: DependencySet = old_base,
                            ) -> None:
                                branch.base_dependency = old_base

                            self._session.trail.record(
                                "rules.branch.support",
                                undo_branch_support,
                            )
                            branch.base_dependency = record.base_dependency
                            self.dispatch_ground_atom(
                                self.atom_for_id(branch.current),
                                record.base_dependency.add(branch.level),
                            )
                return False
        disjunction_id = self._session.add_ground_disjunction(identifiers, dependency)
        self._disjunction_keys[identifiers] = disjunction_id

        def undo() -> None:
            if self._disjunction_keys.get(identifiers) == disjunction_id:
                self._disjunction_keys.pop(identifiers)

        self._session.trail.record("rules.disjunction.key", undo)
        return True

    def _dispatch_equality(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        provenance_ids: tuple[int, ...],
    ) -> bool:
        left, right = atom.arguments
        predicate = self._program.predicates.predicate(atom.predicate_id)
        if self._fixed_data_values_differ((left, right)):
            return self._session.install_clash(
                Clash(
                    ClashKind.EQUALITY_INEQUALITY,
                    dependency,
                    (self.atom_id(atom),),
                )
            )
        inequality_id = self._inequality_by_sort.get(predicate.argument_sorts[0])
        inequality = (
            None if inequality_id is None else self._fact_dependency(inequality_id, (left, right))
        )
        if inequality is not None:
            return self._session.install_clash(
                Clash(
                    ClashKind.EQUALITY_INEQUALITY,
                    self._session.dependencies.union(dependency, inequality),
                    (self.atom_id(atom),),
                )
            )
        changed = False
        if left != right:
            representative = self._session.merge_nodes(left, right, dependency)
            changed = True
        else:
            representative = left
        reflexive = GroundRuleAtom(atom.predicate_id, (representative, representative))
        return self._add_extension_atom(reflexive, dependency, provenance_ids) or changed

    def _dispatch_annotated_equality(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        provenance_ids: tuple[int, ...],
    ) -> bool:
        action_id = self.atom_id(atom)
        existing_id = self._pending_by_atom.get(atom)
        if existing_id is not None:
            previous = self._pending_annotated[existing_id]
            supports = _retain_supports((*previous.supports, dependency))
            provenance = tuple(sorted(set((*previous.provenance_ids, *provenance_ids))))
            if supports == previous.supports and provenance == previous.provenance_ids:
                return False
            updated = replace(previous, supports=supports, provenance_ids=provenance)
            self._session.trail.record(
                "rules.annotated.support",
                lambda: self._pending_annotated.__setitem__(existing_id, previous),
            )
            self._pending_annotated[existing_id] = updated
            return True
        record = PendingAnnotatedEquality(
            action_id,
            atom,
            (self._session.dependencies.intern(dependency),),
            provenance_ids,
        )
        self._pending_annotated[action_id] = record
        self._pending_by_atom[atom] = action_id

        def undo() -> None:
            self._pending_annotated.pop(action_id, None)
            self._pending_by_atom.pop(atom, None)

        self._session.trail.record("rules.annotated.create", undo)
        self._session.annotated_equalities.enqueue(action_id, (action_id,))
        return True

    def _add_extension_atom(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        provenance_ids: tuple[int, ...],
    ) -> bool:
        if len(atom.arguments) not in (1, 2):
            raise InternalInvariantError("extension rows must be unary or binary")
        provenance = tuple(sorted(set(provenance_ids)))
        outcome = self._session.extensions.add(
            atom.predicate_id,
            atom.arguments,
            dependency,
            provenance_id=None if not provenance else provenance[0],
        )
        for provenance_id in provenance[1:]:
            self._session.extensions.add(
                atom.predicate_id,
                atom.arguments,
                dependency,
                provenance_id=provenance_id,
            )
        return outcome.created or outcome.support_changed

    def _derive_concrete_role_inequalities(
        self,
        atom: GroundRuleAtom,
        opposite_predicate_id: int,
        dependency: DependencySet,
        provenance_ids: tuple[int, ...],
    ) -> None:
        """Materialize value inequality implied by positive/negative data-role pairs."""

        source, target = atom.arguments
        inequality_id = self._inequality_by_sort.get(TermSort.DATA)
        for row in self._session.extensions.retrieve(
            opposite_predicate_id,
            bindings={0: source},
        ):
            other = row.key.arguments[1]
            if inequality_id is None:
                if self._fixed_data_values_differ((target, other)):
                    continue
                raise InternalInvariantError(
                    "non-fixed data-role negation requires a compiled inequality predicate"
                )
            for opposite_support in row.supports:
                self.dispatch_ground_atom(
                    GroundRuleAtom(inequality_id, (target, other)),
                    self._session.dependencies.union(dependency, opposite_support),
                    provenance_ids=provenance_ids,
                )

    def _fact_dependency(
        self,
        predicate_id: int,
        arguments: tuple[NodeHandle, ...],
    ) -> DependencySet | None:
        rows = tuple(
            self._session.extensions.retrieve(
                predicate_id,
                bindings={index: value for index, value in enumerate(arguments)},
            )
        )
        supports = tuple(value for row in rows for value in row.supports)
        return None if not supports else min(supports, key=_dependency_rank)

    def _canonical_atom(
        self,
        atom: GroundRuleAtom,
    ) -> tuple[GroundRuleAtom, DependencySet]:
        handles: list[NodeHandle] = []
        dependencies: list[DependencySet] = []
        for handle in atom.arguments:
            representative, path = self._session.nodes.representative(handle)
            self._session.nodes.require_active(representative)
            handles.append(representative)
            dependencies.append(path)
        predicate = self._program.predicates.predicate(atom.predicate_id)
        if (
            predicate.kind
            in {
                PredicateKind.EQUALITY,
                PredicateKind.INEQUALITY,
                PredicateKind.ORDERING_GUARD,
            }
            or predicate.kind is PredicateKind.ANNOTATED_EQUALITY
        ):
            handles[:2] = sorted(handles[:2], key=self._node_rank)
        return (
            GroundRuleAtom(atom.predicate_id, tuple(handles)),
            self._session.dependencies.union(*dependencies),
        )

    def _ground_compiled_atom(
        self,
        atom: GroundAtom,
    ) -> tuple[GroundRuleAtom, DependencySet]:
        arguments: list[NodeHandle] = []
        dependencies: list[DependencySet] = []
        for term in atom.arguments:
            handle, dependency = self._resolve_ground_term(term)
            arguments.append(handle)
            dependencies.append(dependency)
        return (
            self._canonical_atom(GroundRuleAtom(atom.predicate_id, tuple(arguments)))[0],
            self._session.dependencies.union(*dependencies),
        )

    def _ground_atom(
        self,
        atom: Atom,
        bindings: Mapping[tuple[TermSort, int], NodeHandle],
    ) -> tuple[GroundRuleAtom, DependencySet]:
        arguments: list[NodeHandle] = []
        dependencies: list[DependencySet] = []
        for term in atom.arguments:
            if isinstance(term, Variable):
                handle = bindings.get((term.sort, term.index))
                if handle is None:
                    raise InternalInvariantError(
                        "head variable is absent from the join substitution"
                    )
                representative, dependency = self._session.nodes.representative(handle)
                self._session.nodes.require_active(representative)
            else:
                representative, dependency = self._resolve_ground_term(term)
            arguments.append(representative)
            dependencies.append(dependency)
        grounded, canonical_dependency = self._canonical_atom(
            GroundRuleAtom(atom.predicate_id, tuple(arguments))
        )
        return grounded, self._session.dependencies.union(*dependencies, canonical_dependency)

    def _resolve_ground_term(self, term: GroundTerm) -> tuple[NodeHandle, DependencySet]:
        if isinstance(term, IndividualTerm):
            handle = self._source_nodes.get(term.individual_id)
            label = f"individual ID {term.individual_id}"
        elif isinstance(term, DataConstant):
            handle = self._data_nodes.get(term.data_identity_id)
            label = f"data identity ID {term.data_identity_id}"
        else:
            raise TypeError("ground term must be IndividualTerm or DataConstant")
        if handle is None:
            raise InternalInvariantError(f"compiled {label} has no tableau node")
        representative, dependency = self._session.nodes.representative(handle)
        self._session.nodes.require_active(representative)
        return representative, dependency

    def _seed_reflexive_equalities(self) -> None:
        for handle in self._session.nodes.active_handles():
            node = self._session.nodes.get(handle)
            sort = TermSort.OBJECT if node.sort is NodeSort.OBJECT else TermSort.DATA
            predicate_id = self._equality_by_sort.get(sort)
            if predicate_id is not None:
                self._add_extension_atom(
                    GroundRuleAtom(predicate_id, (handle, handle)),
                    self._session.dependencies.empty,
                    (),
                )

    def _fire_unconditional(self, token: CancellationToken) -> None:
        naive = NaiveJoinEvaluator(self._indexed_evaluator(token))
        for clause_id in self._join_program.unconditional_clause_ids:
            for match in naive.matches(clause_id, require_new=False):
                self._apply_match(match)
                if self._session.clashes.current is not None:
                    return

    def _validate_ground_sorts(
        self,
        predicate: Predicate,
        arguments: tuple[NodeHandle, ...],
    ) -> None:
        if len(arguments) != len(predicate.argument_sorts):
            raise InternalInvariantError("ground atom arity disagrees with its predicate")
        for handle, sort in zip(arguments, predicate.argument_sorts, strict=True):
            node = self._session.nodes.require_active(handle)
            expected = NodeSort.OBJECT if sort is TermSort.OBJECT else NodeSort.DATA
            if node.sort is not expected:
                raise InternalInvariantError("ground atom argument has the wrong node sort")

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation

    def _has_clash(self) -> bool:
        return self._session.clashes.current is not None

    def _fixed_data_values_differ(self, arguments: tuple[NodeHandle, ...]) -> bool:
        if len(arguments) != 2:
            return False
        direct = tuple(self._data_identities_by_handle.get(value) for value in arguments)
        if direct[0] is not None and direct[1] is not None:
            return direct[0].isdisjoint(direct[1])
        identities: list[frozenset[int]] = []
        for argument in arguments:
            values = frozenset(
                identifier
                for identifier, handle in self._data_nodes.items()
                if self._session.nodes.representative(handle)[0] == argument
            )
            if not values:
                return False
            identities.append(values)
        return identities[0].isdisjoint(identities[1])

    def _disjunct_rank(self, atom: GroundRuleAtom) -> tuple[object, ...]:
        predicate = self._program.predicates.predicate(atom.predicate_id)
        kind_rank = {
            PredicateKind.EQUALITY: 0,
            PredicateKind.ANNOTATED_EQUALITY: 1,
            PredicateKind.INEQUALITY: 2,
            PredicateKind.CONCEPT: 3,
            PredicateKind.NEGATED_CONCEPT: 3,
            PredicateKind.NOMINAL: 3,
            PredicateKind.NEGATED_NOMINAL: 3,
        }.get(predicate.kind, 4)
        return (
            kind_rank,
            predicate.kind.value,
            atom.predicate_id,
            tuple(self._node_rank(value) for value in atom.arguments),
        )


def _node_map(values: Mapping[int, NodeHandle], name: str) -> dict[int, NodeHandle]:
    result = dict(values)
    if any(
        isinstance(identifier, bool)
        or not isinstance(identifier, int)
        or identifier < 0
        or not isinstance(handle, NodeHandle)
        for identifier, handle in result.items()
    ):
        raise TypeError(f"{name} must map nonnegative IDs to NodeHandle values")
    return result


def _predicates_by_sort(
    program: ClauseProgram,
    kind: PredicateKind,
) -> dict[TermSort, int]:
    return {
        predicate.argument_sorts[0]: predicate.predicate_id
        for predicate in program.predicates.predicates
        if predicate.kind is kind
    }


def _opposite_predicates(program: ClauseProgram) -> dict[int, int]:
    result: dict[int, int] = {}
    by_key: dict[tuple[object, ...], dict[PredicateKind, int]] = {}
    pair_by_kind = {
        kind: (positive, negative)
        for positive, negative in _NEGATION_PAIRS
        for kind in (positive, negative)
    }
    for predicate in program.predicates.predicates:
        pair = pair_by_kind.get(predicate.kind)
        if pair is None:
            continue
        key = (
            pair[0].value,
            predicate.argument_sorts,
            predicate.symbol_id,
            predicate.role_id,
            predicate.annotation,
        )
        by_key.setdefault(key, {})[predicate.kind] = predicate.predicate_id
    for values in by_key.values():
        if len(values) != 2:
            continue
        identifiers = tuple(values.values())
        result[identifiers[0]] = identifiers[1]
        result[identifiers[1]] = identifiers[0]
    for sort, equality in _predicates_by_sort(program, PredicateKind.EQUALITY).items():
        inequality = _predicates_by_sort(program, PredicateKind.INEQUALITY).get(sort)
        if inequality is not None:
            result[equality] = inequality
            result[inequality] = equality
    return result


def _retain_supports(values: tuple[DependencySet, ...]) -> tuple[DependencySet, ...]:
    result: list[DependencySet] = []
    for candidate in sorted(set(values), key=lambda value: value.bits):
        if any(known.is_subset_of(candidate) for known in result):
            continue
        result = [known for known in result if not candidate.is_subset_of(known)]
        result.append(candidate)
    return tuple(sorted(result, key=lambda value: value.bits))


def _dependency_rank(value: DependencySet) -> tuple[int, int, int]:
    maximum = value.maximum
    return len(value), -1 if maximum is None else maximum, value.bits


__all__ = ["HyperresolutionEngine"]
