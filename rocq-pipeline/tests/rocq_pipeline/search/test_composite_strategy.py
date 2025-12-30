from typing import override

# Import the function we want to test
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rollout import Rollout
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


def is_empty[T](x: Rollout[T]) -> None:
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
