import itertools
from typing import override

# Import the function we want to test
import pytest
from rocq_pipeline.search import strategy
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rollout import Rollout
from rocq_pipeline.search.strategy import (
    FailStrategy,
    IteratorStrategy,
    SingletonStrategy,
    StagedStrategy,
    Strategy,
)


class SimpleAction[T](Action[list[T]]):
    def __init__(self, value: T) -> None:
        self._value = value

    @override
    def interact(self, state: list[T]) -> list[T]:
        return state + [self._value]


type ActionL[T] = Action[list[T]]
type RolloutAL[T] = Rollout[ActionL[T]]
type StrategyAL[T] = Strategy[list[T], ActionL[T]]


def is_empty[T](x: RolloutAL[int]) -> None:
    try:
        elem = next(x)
        raise AssertionError(f"empty contains element {elem}")
    except StopIteration:
        pass


def test_empty() -> None:
    strat: StrategyAL[int] = StagedStrategy(FailStrategy(), FailStrategy())
    actions = strat.rollout([])
    is_empty(actions)


def next_eval(actions: RolloutAL[int], st: list[int]) -> tuple[float, list[int]]:
    pr, act = next(actions)
    return (pr, act.interact(st))


def test_empty_1() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        FailStrategy(), SingletonStrategy(SimpleAction(0), 0.5)
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    is_empty(actions)


def test_empty_2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5), FailStrategy()
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    is_empty(actions)


def test_both_1() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    assert (0.75, [1]) == next_eval(actions, [])
    is_empty(actions)


def test_both_2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
        prob=0.5,
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    assert (0.75, [1]) == next_eval(actions, [])
    is_empty(actions)


def test_both_3() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
        prob=0.8,
    )
    actions = strat.rollout([])
    assert (0.75, [1]) == next_eval(actions, [])
    assert (0.5, [0]) == next_eval(actions, [])
    is_empty(actions)


def test_both_4() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        IteratorStrategy([(0.5, SimpleAction(0)), (0.4, SimpleAction(1))]),
        SingletonStrategy(SimpleAction(2), 0.75),
        prob=0.2,
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    assert (0.4, [1]) == next_eval(actions, [])
    assert (0.75, [2]) == next_eval(actions, [])
    is_empty(actions)


class NeverStrategy[T, A](Strategy[T, A]):
    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[A]:
        raise AssertionError("Should not Run")


def test_delayed() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        NeverStrategy(),
        prob=0.3,
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])


def test_delayed_edge() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        NeverStrategy(),
        prob=0.5,
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])


def test_delayed_edge2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        IteratorStrategy([(0.5, SimpleAction(0)), (0.4, SimpleAction(1))]),
        NeverStrategy(),
        prob=0.2,
    )
    actions = strat.rollout([])
    assert (0.5, [0]) == next_eval(actions, [])
    assert (0.4, [1]) == next_eval(actions, [])


VALUES = [
    ([(None, []), (None, []), (None, [])], []),
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (None, [(0.95, 4), (0.85, 5), (0.2, 6)]),
            (None, []),
        ],
        [(0.9, 1), (0.8, 2), (0.7, 3), (0.95, 4), (0.85, 5), (0.2, 6)],
    ),
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (0.8, [(0.95, 4), (0.85, 5), (0.2, 6)]),
            (None, []),
        ],
        [(0.9, 1), (0.8, 2), (0.95, 4), (0.85, 5), (0.7, 3), (0.2, 6)],
    ),
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (0.7, [(0.95, 4), (0.85, 5), (0.2, 6)]),
            (None, []),
        ],
        [(0.9, 1), (0.8, 2), (0.7, 3), (0.95, 4), (0.85, 5), (0.2, 6)],
    ),
    ####
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (0.8, []),
            (0.8, [(0.95, 4), (0.85, 5), (0.2, 6)]),
            (None, []),
        ],
        [(0.9, 1), (0.8, 2), (0.95, 4), (0.85, 5), (0.7, 3), (0.2, 6)],
    ),
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (0.9, []),
            (0.8, [(0.95, 4), (0.85, 5), (0.2, 6)]),
        ],
        [(0.9, 1), (0.95, 4), (0.85, 5), (0.8, 2), (0.7, 3), (0.2, 6)],
    ),
    (
        [
            (None, [(0.9, 1), (0.8, 2), (0.7, 3)]),
            (0.9, [(0.3, 9)]),
            (0.8, [(0.95, 4), (0.85, 5), (0.2, 6)]),
        ],
        [(0.9, 1), (0.95, 4), (0.85, 5), (0.8, 2), (0.7, 3), (0.3, 9), (0.2, 6)],
    ),
]


@pytest.mark.parametrize("lls, expected", VALUES, ids=[str(x) for _, x in VALUES])
def test_many(
    lls: list[tuple[float, list[tuple[float, int]]]], expected: list[tuple[float, int]]
):
    strat: StrategyAL[int] = strategy.staged(
        [
            (cutoff, IteratorStrategy([(prob, SimpleAction(i)) for prob, i in x]))
            for cutoff, x in lls
        ]
    )

    result: list[tuple[float, int]] = []
    for _ in range(0, 2):
        result = [(prob, n.interact([])[0]) for prob, n in strat.rollout([])]
        assert result == expected

    for pre_len in range(0, len(result)):
        x = [
            (prob, n.interact([])[0])
            for prob, n in itertools.islice(strat.rollout([]), pre_len)
        ]
        assert x == expected[:pre_len]
