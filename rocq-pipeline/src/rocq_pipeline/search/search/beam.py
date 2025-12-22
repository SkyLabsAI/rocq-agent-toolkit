from __future__ import annotations

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import Strategy


class SearchNode[T]:
    id: int  # Unique id
    parent_id: int | None
    depth: int
    state: T

    # Cost information
    cost_score: float = float("inf")
    cumulative_log_prob: float = 0.0

    def __init__(self) -> None:
        pass

    @classmethod
    def make_root(cls, state: T) -> SearchNode[T]:
        result: SearchNode[T] = SearchNode()
        result.id = cls._fresh_id()
        result.parent_id = None
        result.depth = 0
        result.state = state
        return result

    def make_child(self, state: T, cost_score: float, log_prob: float) -> SearchNode[T]:
        result: SearchNode[T] = SearchNode()
        result.id = SearchNode._fresh_id()
        result.parent_id = self.id
        result.depth = self.depth + 1
        result.cost_score = cost_score
        result.cumulative_log_prob = log_prob
        result.state = state
        return result

    def is_solved(self) -> bool:
        # TODO: implement this. It needs to be a method on the underlying state object or on the dynamics
        return False

    _counter: int = 0

    @classmethod
    def _fresh_id(cls) -> int:
        result = cls._counter
        cls._counter += 1
        return result


class StateManip[T]:
    def freshen(self, state: T) -> T:
        return state

    def dispose(self, state: T) -> None:
        return None


class BeamSearch[T]:
    """
    A simple implementation of the Beam search.

    """

    def __init__(
        self,
        strategy: Strategy[T],
        beam_width: int = 5,
        beam_count: int = 10,
        freshen: StateManip[T]
        | None = None,  # the StateManip is a hack to get around the fact that RocqCursor is imperative
    ) -> None:
        self._strategy = strategy
        self._beam_width = beam_width
        self._max_depth = 10
        self._beam_count = beam_count
        self._freshen = freshen or StateManip()

    def search(self, state: T) -> list[SearchNode[T]]:
        root = SearchNode.make_root(state)

        frontier: list[SearchNode[T]] = [root]
        solutions: list[SearchNode[T]] = []

        for _ in range(self._max_depth):
            nodes_to_expand = self._take(frontier)
            next_frontier: list[SearchNode[T]] = []

            for node in nodes_to_expand:
                expanded = self._expand(node)
                next_frontier.extend(expanded)

            solutions.extend([node for node in next_frontier if node.is_solved()])
            frontier = next_frontier

        return solutions

    def _take(self, frontier: list[SearchNode[T]]) -> list[SearchNode[T]]:
        frontier.sort(key=lambda n: n.cost_score)
        return frontier[: self._beam_count]

    def _expand(self, node: SearchNode[T]) -> list[SearchNode[T]]:
        result: list[SearchNode[T]] = []
        for prob, action in self._strategy.rollout(
            node.state, max_rollout=self._beam_width
        ):
            fresh_state = self._freshen.freshen(node.state)
            try:
                new_state = action.interact(fresh_state)
            except Action.Failed:
                self._freshen.dispose(fresh_state)
                continue

            result.append(node.make_child(new_state, 0, prob))

        return result
