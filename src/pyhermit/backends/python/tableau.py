"""Complete phase scheduler for one pure-Python hypertableau run.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass

from pyhermit.backends.python.blocking import (
    BlockingManager,
    BlockingRequirements,
    BlockingVocabulary,
    create_direct_checker,
    select_blocking_plan,
)
from pyhermit.backends.python.blocking.validation import CompiledClauseBlockingValidator
from pyhermit.backends.python.datatype_manager import TableauDatatypeManager
from pyhermit.backends.python.existentials import (
    ExistentialExpansionManager,
    ExpansionStatus,
    ExpansionStrategy,
)
from pyhermit.backends.python.merging import MergingManager
from pyhermit.backends.python.nominals import NominalIntroductionManager
from pyhermit.backends.python.rules import BranchTransition, HyperresolutionEngine
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, SymbolKind
from pyhermit.config import ExistentialMode, ReasonerConfig
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError


@dataclass(frozen=True, slots=True)
class TableauLimits:
    max_scheduler_steps: int = 10_000_000

    def __post_init__(self) -> None:
        if (
            isinstance(self.max_scheduler_steps, bool)
            or not isinstance(self.max_scheduler_steps, int)
            or self.max_scheduler_steps <= 0
        ):
            raise ValueError("max_scheduler_steps must be a positive integer")


@dataclass(frozen=True, slots=True)
class TableauRunStatistics:
    scheduler_steps: int = 0
    delta_generations: int = 0
    existential_actions: int = 0
    nominal_actions: int = 0
    disjunction_actions: int = 0
    datatype_checks: int = 0
    backtracks: int = 0

    def __post_init__(self) -> None:
        for name in (
            "scheduler_steps",
            "delta_generations",
            "existential_actions",
            "nominal_actions",
            "disjunction_actions",
            "datatype_checks",
            "backtracks",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")


@dataclass(frozen=True, slots=True)
class TableauRunResult:
    satisfiable: bool
    statistics: TableauRunStatistics

    def __post_init__(self) -> None:
        if not isinstance(self.satisfiable, bool):
            raise TypeError("satisfiable must be bool")
        if not isinstance(self.statistics, TableauRunStatistics):
            raise TypeError("statistics must be TableauRunStatistics")


class PythonTableau:
    """Own and saturate one isolated compiled program."""

    __slots__ = (
        "blocking",
        "config",
        "data_nodes",
        "datatypes",
        "engine",
        "existentials",
        "limits",
        "merger",
        "nominals",
        "program",
        "session",
        "source_nodes",
        "validator",
    )

    def __init__(
        self,
        program: ClauseProgram,
        config: ReasonerConfig,
        token: CancellationToken,
        *,
        limits: TableauLimits | None = None,
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        if not isinstance(config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig")
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        selected_limits = TableauLimits() if limits is None else limits
        if not isinstance(selected_limits, TableauLimits):
            raise TypeError("limits must be TableauLimits or None")
        token.check()
        self.program = program
        self.config = config
        self.limits = selected_limits
        self.session = TableauSession()
        self.source_nodes = self._create_source_nodes()
        self.data_nodes = self._create_data_nodes()
        if not self.source_nodes:
            self.session.create_node(NodeKind.ROOT)
        self.engine = HyperresolutionEngine(
            program,
            self.session,
            source_nodes=self.source_nodes,
            data_nodes=self.data_nodes,
            disjunction_learning=config.disjunction_learning,
        )
        self.merger = MergingManager(self.session, self.engine)
        self.engine.set_merging_manager(self.merger)
        strategy = (
            ExpansionStrategy.INDIVIDUAL_REUSE
            if config.existentials is ExistentialMode.INDIVIDUAL_REUSE
            else ExpansionStrategy.CREATION_ORDER
        )
        self.existentials = ExistentialExpansionManager(
            self.session,
            self.engine,
            strategy=strategy,
        )
        self.nominals = NominalIntroductionManager(
            self.session,
            self.engine,
            self.merger,
        )
        requirements = BlockingRequirements.from_program(program)
        plan = select_blocking_plan(config.blocking, requirements)
        vocabulary = BlockingVocabulary.from_program(program)
        checker = create_direct_checker(
            plan.direct_checker_kind,
            vocabulary,
            has_inverses=program.expressivity.inverse_roles,
        )
        self.blocking = BlockingManager(self.session, checker, plan)
        self.validator = (
            CompiledClauseBlockingValidator(program, core_mode=plan.core_mode)
            if plan.validated
            else None
        )
        self.datatypes = TableauDatatypeManager(
            program,
            self.session,
            data_nodes=self.data_nodes,
        )
        self.engine.initialize(token)

    def run(self, token: CancellationToken) -> TableauRunResult:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        steps = 0
        deltas = 0
        existential_actions = 0
        nominal_actions = 0
        disjunction_actions = 0
        datatype_checks = 0
        backtracks = 0

        while True:
            steps += 1
            if steps > self.limits.max_scheduler_steps:
                raise ResourceLimitError(
                    "tableau scheduler step limit exceeded",
                    limit="max_scheduler_steps",
                    observed=steps,
                    allowed=self.limits.max_scheduler_steps,
                )
            token.add_work(1)
            token.check()

            if self.session.clashes.current is None:
                processed_nominals = self.nominals.process_all(token)
                nominal_actions += processed_nominals
                if processed_nominals:
                    continue

                processed_delta = self.engine.apply_next_delta(token)
                if processed_delta:
                    deltas += 1
                    datatype_result = self.datatypes.check(token)
                    datatype_checks += datatype_result.checked_components
                    if self.session.clashes.current is None:
                        processed_nominals = self.nominals.process_all(token)
                        nominal_actions += processed_nominals
                    continue

                datatype_result = self.datatypes.check(token)
                datatype_checks += datatype_result.checked_components
                if datatype_result.changed and datatype_result.clashed:
                    continue

                if len(self.session.existential_candidates):
                    self._refresh_blocking()
                expansion = self.existentials.process_next(token)
                if expansion.status in {
                    ExpansionStatus.EXPANDED,
                    ExpansionStatus.SATISFIED,
                    ExpansionStatus.CLASHED,
                }:
                    existential_actions += 1
                    continue

                transition = self.engine.process_next_disjunction(token)
                if transition is not BranchTransition.NO_WORK:
                    disjunction_actions += 1
                    continue

            if self.session.clashes.current is not None:
                transition = self._resolve_clash(token)
                if transition is BranchTransition.UNSAT:
                    return TableauRunResult(
                        False,
                        TableauRunStatistics(
                            steps,
                            deltas,
                            existential_actions,
                            nominal_actions,
                            disjunction_actions,
                            datatype_checks,
                            backtracks,
                        ),
                    )
                backtracks += 1
                self.datatypes.invalidate()
                self.blocking.invalidate()
                continue

            if self.validator is not None:
                has_active_tree = any(
                    node.kind is NodeKind.TREE and node.lifecycle is NodeLifecycle.ACTIVE
                    for node in self.session.nodes.existing_nodes()
                )
                if has_active_tree:
                    validation = self.blocking.validation_pass(self.validator, token=token)
                    if not validation.valid:
                        continue
            if not self.blocking.ready_for_sat():
                raise InternalInvariantError(
                    "validated blocking requires a validator before SAT completion"
                )
            self.session.check_invariants()
            return TableauRunResult(
                True,
                TableauRunStatistics(
                    steps,
                    deltas,
                    existential_actions,
                    nominal_actions,
                    disjunction_actions,
                    datatype_checks,
                    backtracks,
                ),
            )

    def _resolve_clash(self, token: CancellationToken) -> BranchTransition:
        clash = self.session.clashes.current
        if clash is None:
            return BranchTransition.NO_WORK
        level = clash.dependency.maximum
        if level is None:
            return BranchTransition.UNSAT
        if not 0 <= level < len(self.session.branches):
            raise InternalInvariantError("clash dependency has no live branching point")
        branch = self.session.branches[level]
        if branch.choice_kind is BranchChoiceKind.GROUND_DISJUNCTION:
            return self.engine.brancher.resolve_clash(token)
        if branch.choice_kind is BranchChoiceKind.MERGE:
            transition = self.nominals.resolve_clash(token)
            if transition is not BranchTransition.NO_WORK:
                return transition
            return self.existentials.resolve_clash(token)
        raise InternalInvariantError("datatype branching is not owned by the Python scheduler")

    def _refresh_blocking(self) -> None:
        while True:
            handle = self.session.blocking_invalidations.pop()
            if handle is None:
                break
            self.blocking.invalidate(handle)
        self.blocking.compute()

    def _create_source_nodes(self) -> dict[int, NodeHandle]:
        result: dict[int, NodeHandle] = {}
        domain = self.program.symbols.domain(SymbolKind.INDIVIDUAL)
        for value in domain.values:
            named = value.display.startswith("named_individual:")
            result[value.identifier] = self.session.create_node(
                NodeKind.ROOT,
                is_owl_named_individual=named,
                source_individual_id=value.identifier if named else None,
            )
        return result

    def _create_data_nodes(self) -> dict[int, NodeHandle]:
        return {
            value.identifier: self.session.create_node(NodeKind.CONCRETE)
            for value in self.program.symbols.domain(SymbolKind.DATA_VALUE).values
        }


__all__ = [
    "PythonTableau",
    "TableauLimits",
    "TableauRunResult",
    "TableauRunStatistics",
]
