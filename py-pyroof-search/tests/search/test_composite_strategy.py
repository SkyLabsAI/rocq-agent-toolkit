from typing import override

# Import the function we want to test
import pytest
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rollout import Rollout
from rocq_pipeline.search.strategy import (
    CompositeStrategy,
    FailStrategy,
    IteratorStrategy,
    SingletonStrategy,
    Strategy,
)

from .rollout_util import is_empty

pytestmark = pytest.mark.asyncio


class SimpleAction[T](Action[list[T]]):
    def __init__(self, value: T) -> None:
        self._value = value

    @override
    async def interact(self, state: list[T]) -> list[T]:
        return state + [self._value]


async def take_n[T](x: Rollout[T], n: int) -> list[tuple[float, T]]:
    out: list[tuple[float, T]] = []
    for _ in range(n):
        proposal = await x.next()
        if proposal.result is None:
            continue
        out.append((proposal.logprob, proposal.result))
    return out


async def take_all[T](x: Rollout[T]) -> list[tuple[float, T]]:
    out: list[tuple[float, T]] = []
    while True:
        try:
            proposal = await x.next()
        except StopAsyncIteration:
            return out
        if proposal.result is None:
            continue
        out.append((proposal.logprob, proposal.result))


type ActionStrategy = Strategy[list[int], Action[list[int]]]


async def test_empty() -> None:
    strat: ActionStrategy = CompositeStrategy([])
    actions = await strat.rollout([])
    await is_empty(actions)


async def test_empty_empty() -> None:
    strat: ActionStrategy = CompositeStrategy([FailStrategy()])
    actions = await strat.rollout([])
    await is_empty(actions)


async def test_empty_empty_empty() -> None:
    strat: ActionStrategy = CompositeStrategy([FailStrategy(), FailStrategy()])
    actions = await strat.rollout([])
    await is_empty(actions)


async def test_singleton() -> None:
    strat: ActionStrategy = CompositeStrategy([SingletonStrategy(SimpleAction(0), 0.5)])
    actions = await strat.rollout([])

    pairs = await take_all(actions)
    assert [(prob, await n.interact([])) for prob, n in pairs] == [(0.5, [0])]

    await is_empty(actions)


async def test_multi() -> None:
    strat: ActionStrategy = CompositeStrategy(
        [
            SingletonStrategy(SimpleAction(0), 0.5),
            SingletonStrategy(SimpleAction(1), 0.75),
        ],
    )
    actions = await strat.rollout([])

    pairs = await take_all(actions)
    assert [(prob, await n.interact([])) for prob, n in pairs] == [
        (0.75, [1]),
        (0.5, [0]),
    ]

    await is_empty(actions)


async def test_multi2() -> None:
    ls: list[ActionStrategy] = [
        IteratorStrategy(iter([(0.5, SimpleAction(0)), (0.25, SimpleAction(2))])),
        SingletonStrategy(SimpleAction(1), 0.75),
    ]
    strat = CompositeStrategy(ls)
    actions = await strat.rollout([])

    pairs = await take_all(actions)
    assert [(prob, await n.interact([])) for prob, n in pairs] == [
        (0.75, [1]),
        (0.5, [0]),
        (0.25, [2]),
    ]

    await is_empty(actions)


async def test_multi_same() -> None:
    ls: list[ActionStrategy] = [
        SingletonStrategy(SimpleAction(1), 0.75),
        SingletonStrategy(SimpleAction(2), 0.75),
        SingletonStrategy(SimpleAction(3), 0.75),
    ]
    strat = CompositeStrategy(ls)
    actions = await strat.rollout([])

    pairs = await take_all(actions)
    result = [(prob, await n.interact([])) for prob, n in pairs]
    assert (0.75, [1]) in result
    assert (0.75, [2]) in result
    assert (0.75, [3]) in result

    await is_empty(actions)


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
async def test_many(
    lls: list[list[tuple[float, int]]], expected: list[tuple[float, int]]
) -> None:
    strat: Strategy[list[int], Action[list[int]]] = CompositeStrategy(
        [IteratorStrategy([(prob, SimpleAction(i)) for prob, i in x]) for x in lls]
    )

    result: list[tuple[float, int]] = []

    # make sure we get the same results more than once
    for _ in range(2):
        rollout = await strat.rollout([])
        pairs = await take_all(rollout)
        result = [(prob, (await n.interact([]))[0]) for prob, n in pairs]
        assert result == expected

    for pre_len in range(len(result)):
        rollout = await strat.rollout([])
        pairs = await take_n(rollout, pre_len)
        x = [(prob, (await n.interact([]))[0]) for prob, n in pairs]
        assert x == expected[:pre_len]
