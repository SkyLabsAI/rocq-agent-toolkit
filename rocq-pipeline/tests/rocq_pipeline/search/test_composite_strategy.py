from typing import override

# Import the function we want to test
import pytest
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import (
    CompositeStrategy,
    FailStrategy,
    IteratorStrategy,
    SingletonStrategy,
    Strategy,
)


class SimpleAction[T](Action[list[T]]):
    def __init__(self, value: T) -> None:
        self._value = value

    @override
    def interact(self, state: list[T]) -> list[T]:
        return state + [self._value]


def is_empty[T](x: Strategy.Rollout[T]) -> None:
    try:
        elem = next(x)
        raise AssertionError(f"empty contains element {elem}")
    except StopIteration:
        pass


def test_empty() -> None:
    strat: Strategy[list[int]] = CompositeStrategy([])
    actions = strat.rollout([])
    is_empty(actions)


def test_empty_empty() -> None:
    strat: Strategy[list[int]] = CompositeStrategy([FailStrategy()])
    actions = strat.rollout([])
    is_empty(actions)


def test_empty_empty_empty() -> None:
    strat: Strategy[list[int]] = CompositeStrategy([FailStrategy(), FailStrategy()])
    actions = strat.rollout([])
    is_empty(actions)


def test_singleton() -> None:
    strat: Strategy[list[int]] = CompositeStrategy(
        [SingletonStrategy(SimpleAction(0), 0.5)]
    )
    actions = strat.rollout([])

    assert [(prob, n.interact([])) for prob, n in actions] == [(0.5, [0])]

    is_empty(actions)


def test_multi() -> None:
    strat: Strategy[list[int]] = CompositeStrategy(
        [
            SingletonStrategy(SimpleAction(0), 0.5),
            SingletonStrategy(SimpleAction(1), 0.75),
        ],
    )
    actions = strat.rollout([])

    assert [(prob, n.interact([])) for prob, n in actions] == [(0.75, [1]), (0.5, [0])]

    is_empty(actions)


def test_multi2() -> None:
    ls: list[Strategy[list[int]]] = [
        IteratorStrategy(iter([(0.5, SimpleAction(0)), (0.25, SimpleAction(2))])),
        SingletonStrategy(SimpleAction(1), 0.75),
    ]
    strat: Strategy[list[int]] = CompositeStrategy(ls)
    actions = strat.rollout([])

    assert [(prob, n.interact([])) for prob, n in actions] == [
        (0.75, [1]),
        (0.5, [0]),
        (0.25, [2]),
    ]

    is_empty(actions)


def test_multi_same() -> None:
    ls: list[Strategy[list[int]]] = [
        SingletonStrategy(SimpleAction(1), 0.75),
        SingletonStrategy(SimpleAction(2), 0.75),
        SingletonStrategy(SimpleAction(3), 0.75),
    ]
    strat: Strategy[list[int]] = CompositeStrategy(ls)
    actions = strat.rollout([])

    result = [(prob, n.interact([])) for prob, n in actions]
    assert (0.75, [1]) in result
    assert (0.75, [2]) in result
    assert (0.75, [3]) in result

    is_empty(actions)


VALUES = [
    ([[], [], []], []),
    (
        [[(0.9, 1), (0.8, 2), (0.7, 3)], [(0.95, 4), (0.85, 5), (0.2, 6)], []],
        [(0.95, 4), (0.9, 1), (0.85, 5), (0.8, 2), (0.7, 3), (0.2, 6)],
    ),
    (
        [[], [(0.9, 1), (0.8, 2), (0.7, 3)], [], [(0.95, 4), (0.85, 5), (0.2, 6)], []],
        [(0.95, 4), (0.9, 1), (0.85, 5), (0.8, 2), (0.7, 3), (0.2, 6)],
    ),
    (
        [[], [], [(0.95, 4), (0.85, 5), (0.2, 6)], [(0.9, 1), (0.8, 2), (0.7, 3)], []],
        [(0.95, 4), (0.9, 1), (0.85, 5), (0.8, 2), (0.7, 3), (0.2, 6)],
    ),
    (
        [[], [], [(0.95, 4), (0.85, 5), (0.2, 6)], [(0.9, 1), (0.7, 3)], []],
        [(0.95, 4), (0.9, 1), (0.85, 5), (0.7, 3), (0.2, 6)],
    ),
    (
        [[], [], [(0.95, 4), (0.2, 6)], [(0.9, 1), (0.8, 2), (0.7, 3)], []],
        [(0.95, 4), (0.9, 1), (0.8, 2), (0.7, 3), (0.2, 6)],
    ),
    (
        [[], [], [(0.95, 4)], [(0.9, 1), (0.8, 2), (0.7, 3)], []],
        [(0.95, 4), (0.9, 1), (0.8, 2), (0.7, 3)],
    ),
    (
        [
            [],
            [],
            [(0.95, 1), (0.95, 1), (0.8, 6)],
            [(0.95, 1), (0.95, 1), (0.7, 3)],
            [],
        ],
        [(0.95, 1), (0.95, 1), (0.95, 1), (0.95, 1), (0.8, 6), (0.7, 3)],
    ),
    (
        [
            [],
            [],
            [(0.95, 1), (0.95, 2), (0.8, 6)],
            [(0.95, 1), (0.95, 2), (0.7, 3)],
            [],
        ],
        # this is not strictly necessary, we could do 1,1,2,2
        [(0.95, 1), (0.95, 2), (0.95, 1), (0.95, 2), (0.8, 6), (0.7, 3)],
    ),
]


@pytest.mark.parametrize("lls, expected", VALUES, ids=[str(x) for _, x in VALUES])
def test_many(lls: list[list[tuple[float, int]]], expected: list[tuple[float, int]]):
    strat = CompositeStrategy(
        [IteratorStrategy([(prob, SimpleAction(i)) for prob, i in x]) for x in lls]
    )
    result = [(prob, n.interact([])[0]) for prob, n in strat.rollout([])]

    assert result == expected
