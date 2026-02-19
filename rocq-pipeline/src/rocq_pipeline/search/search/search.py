from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from observability import trace_context

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rollout import Rollout
from rocq_pipeline.search.strategy import Strategy

from .frontier import BasicNode, Frontier


@dataclass(frozen=True)
class RepetitionPolicy:
    """Thresholds for detecting action repetition patterns."""

    max_consecutive: int
    min_pattern_len: int
    max_pattern_len: int
    min_reps: int

    def history_limit(self) -> int:
        return max(self.max_consecutive + 1, self.max_pattern_len * self.min_reps)


def _has_action_repetition(
    actions: list[str], policy: RepetitionPolicy
) -> tuple[bool, str | None]:
    """Detect repeated action patterns in the tail of an action list."""
    if len(actions) < policy.max_consecutive:
        return False, None

    # Detect runs of the same action.
    if len(actions) > policy.max_consecutive:
        last = actions[-policy.max_consecutive - 1 :]
        if len(set(last)) == 1:
            return True, f"consecutive_{policy.max_consecutive}"

    # Detect short cycles that repeat min_reps times.
    for pattern_len in range(
        policy.min_pattern_len,
        min(policy.max_pattern_len + 1, len(actions) // policy.min_reps + 1),
    ):
        if len(actions) < pattern_len * policy.min_reps:
            continue

        pattern = actions[-pattern_len:]
        is_repeating = True
        for i in range(2, policy.min_reps + 1):
            start = -i * pattern_len
            end = -(i - 1) * pattern_len if i > 1 else None
            segment = actions[start:end]
            if segment != pattern:
                is_repeating = False
                break

        if is_repeating:
            return True, f"cyclic_len{pattern_len}"

    return False, None


class Node[CNode]:
    """Search tree node with minimal action history for pruning."""

    depth: int
    parent: Node[CNode] | None
    state: CNode
    _rollout: Rollout[Action[CNode]] | None
    _action_key: str | None
    _seen_action_keys: set[str]

    def __init__(
        self, state: CNode, parent: Node[CNode] | None, action_key: str | None = None
    ) -> None:
        self.depth = 0 if parent is None else (1 + parent.depth)
        self.state = state
        self.parent = parent
        self._rollout = None
        self._action_key = action_key
        self._seen_action_keys = set()

    async def rollout(
        self, strategy: Strategy[CNode, Action[CNode]], **kwargs
    ) -> Rollout[Action[CNode]]:
        # Cache the rollout per node to avoid re-asking the strategy.
        if self._rollout is None:
            self._rollout = await strategy.rollout(self.state, **kwargs)
        return self._rollout

    def update_rollout(self, rollout: Rollout[Action[CNode]]) -> None:
        self._rollout = rollout

    def remember_action(self, key: str) -> bool:
        # Dedup actions at the node scope.
        if key in self._seen_action_keys:
            return True
        self._seen_action_keys.add(key)
        return False

    def recent_action_keys(self, limit: int) -> list[str]:
        keys: list[str] = []
        node: Node[CNode] | None = self
        # Walk parents to recover the last [limit] action keys.
        while node is not None and len(keys) < limit:
            if node._action_key is not None:
                keys.append(node._action_key)
            node = node.parent
        keys.reverse()
        return keys


class StateManipulator[T]:
    """
    State manipulators, these can be used to make states with
    imperative semantics appear more functional.
    """

    async def copy(self, state: T) -> T:
        """Copy"""
        return state

    async def dispose(self, state: T) -> None:
        """Destroy"""
        return None


class Search[CState, FNode: BasicNode]:  # this is `BasicNode[CState]`
    # This class seems to just help type checking a bit.
    @staticmethod
    async def search[FrontierT: Frontier[Node[CState], FNode]](
        strategy: Strategy[CState, Action[CState]],
        start: CState,
        frontier: Callable[[], FrontierT],
        beam_width: int = 1,
        explore_width: int = 1,
        *,
        repetition_policy: RepetitionPolicy | None = None,
        state_manip: StateManipulator[CState] | None = None,
        max_depth: int | None = None,
    ) -> FrontierT:
        worklist: FrontierT = frontier()
        with trace_context("search") as span:
            root = await worklist.push(Node(start, None), None)
            span.set_attribute("root_id", root.ident)
            return await Search.continue_search(
                strategy,
                worklist,
                beam_width=beam_width,
                explore_width=explore_width,
                repetition_policy=repetition_policy,
                state_manip=state_manip,
                max_depth=max_depth,
            )

    @staticmethod
    async def continue_search[FrontierT: Frontier[Node[CState], FNode]](
        strategy: Strategy[CState, Action[CState]],
        worklist: FrontierT,
        beam_width: int = 1,
        explore_width: int = 1,
        *,
        repetition_policy: RepetitionPolicy | None = None,
        state_manip: StateManipulator[CState] | None = None,
        max_depth: int | None = None,
    ) -> FrontierT:
        """Expand a frontier by applying up to explore_width actions per node and pruning duplicates."""
        assert explore_width > 0
        history_limit = repetition_policy.history_limit() if repetition_policy else 0
        # Injected hooks keep search domain-agnostic while preserving resource lifetimes.
        # Defaults use duck-typed clone/interact/dispose when available.
        smanip = state_manip or StateManipulator()

        while True:
            # Sample the beam width from the frontier
            candidates = await worklist.take(count=beam_width)
            if not candidates:
                # Terminate if there are no candidates.
                # This implies that the frontier is empty
                return worklist

            async def process(
                candidate: Node[CState], parent: FNode, action: Action[CState]
            ) -> None:
                with trace_context("search/process") as span:
                    span.set_attribute("parent", parent.ident)
                    span.set_attribute("action", action.key())
                    # Check depth limit before processing
                    if max_depth is not None and candidate.depth > max_depth:
                        return

                    action_key = action.key().strip()
                    # Skip if we've already tried this action from the same node.
                    if candidate.remember_action(action_key):
                        return

                    if repetition_policy is not None:
                        # Guard against local action loops within a bounded history window.
                        history = candidate.recent_action_keys(history_limit - 1)
                        rep_hit, _ = _has_action_repetition(
                            history + [action_key], repetition_policy
                        )
                        if rep_hit:
                            return

                    # clone_state must return a state that is safe to discard without
                    # affecting the parent; apply_action should return the state to enqueue.
                    fresh_state = await smanip.copy(candidate.state)
                    try:
                        next_state = await action.interact(fresh_state)
                        new_node = Node(next_state, candidate, action_key=action_key)
                        # Enqueue the child for future expansion.
                        node = await worklist.push(new_node, parent)
                        span.set_attribute("id", node.ident)
                    except Action.Failed:
                        await smanip.dispose(fresh_state)

            # Rollout each node independently so explore_width is per node.
            for node, parent in candidates:
                if max_depth is not None and node.depth > max_depth:
                    continue
                rollout = await node.rollout(strategy, max_rollout=explore_width)
                count = 0
                async for _, action in rollout:
                    count += 1
                    await process(node, parent, action)
                    # If we got to the end of the iterator, then there might
                    # be more.
                    if count == explore_width:
                        node.update_rollout(rollout)
                        await worklist.repush(parent)
                        break


search = Search.search
continue_search = Search.continue_search
