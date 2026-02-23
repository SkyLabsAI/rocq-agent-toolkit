from typing import override

# Import the function we want to test
import pytest
from pyroof_search import strategy
from pyroof_search.action import Action
from pyroof_search.rollout import Rollout
from pyroof_search.strategy import (
    FailStrategy,
    IteratorStrategy,
    SingletonStrategy,
    StagedStrategy,
    Strategy,
)

from .rollout_util import is_empty


class SimpleAction[T](Action[list[T]]):
    def __init__(self, value: T) -> None:
        self._value = value

    @override
    async def interact(self, state: list[T]) -> list[T]:
        return state + [self._value]


type ActionL[T] = Action[list[T]]
type RolloutAL[T] = Rollout[ActionL[T]]
type StrategyAL[T] = Strategy[list[T], ActionL[T]]


async def take_n[T](x: RolloutAL[T], n: int) -> list[tuple[float, ActionL[T]]]:
    out: list[tuple[float, ActionL[T]]] = []
    for _ in range(n):
        proposal = await x.next()
        if proposal.result is None:
            continue
        out.append((proposal.logprob, proposal.result))
    return out


async def take_all[T](x: RolloutAL[T]) -> list[tuple[float, ActionL[T]]]:
    out: list[tuple[float, ActionL[T]]] = []
    while True:
        try:
            proposal = await x.next()
        except StopAsyncIteration:
            return out
        if proposal.result is None:
            continue
        out.append((proposal.logprob, proposal.result))


@pytest.mark.asyncio
async def test_empty() -> None:
    strat: StrategyAL[int] = StagedStrategy(FailStrategy(), FailStrategy())
    actions = await strat.rollout([])
    await is_empty(actions)


async def next_eval(actions: RolloutAL[int], st: list[int]) -> tuple[float, list[int]]:
    proposal = await actions.next()
    assert proposal.result is not None
    return (proposal.logprob, await proposal.result.interact(st))


@pytest.mark.asyncio
async def test_empty_1() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        FailStrategy(), SingletonStrategy(SimpleAction(0), 0.5)
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    await is_empty(actions)


@pytest.mark.asyncio
async def test_empty_2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5), FailStrategy()
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    await is_empty(actions)


@pytest.mark.asyncio
async def test_both_1() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    assert (0.75, [1]) == await next_eval(actions, [])
    await is_empty(actions)


@pytest.mark.asyncio
async def test_both_2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
        prob=0.5,
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    assert (0.75, [1]) == await next_eval(actions, [])
    await is_empty(actions)


@pytest.mark.asyncio
async def test_both_3() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        SingletonStrategy(SimpleAction(1), 0.75),
        prob=0.8,
    )
    actions = await strat.rollout([])
    assert (0.75, [1]) == await next_eval(actions, [])
    assert (0.5, [0]) == await next_eval(actions, [])
    await is_empty(actions)


@pytest.mark.asyncio
async def test_both_4() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        IteratorStrategy([(0.5, SimpleAction(0)), (0.4, SimpleAction(1))]),
        SingletonStrategy(SimpleAction(2), 0.75),
        prob=0.2,
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    assert (0.4, [1]) == await next_eval(actions, [])
    assert (0.75, [2]) == await next_eval(actions, [])
    await is_empty(actions)


class NeverStrategy[T, A](Strategy[T, A]):
    @override
    async def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[A]:
        raise AssertionError("Should not Run")


@pytest.mark.asyncio
async def test_delayed() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        NeverStrategy(),
        prob=0.3,
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])


@pytest.mark.asyncio
async def test_delayed_edge() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        SingletonStrategy(SimpleAction(0), 0.5),
        NeverStrategy(),
        prob=0.5,
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])


@pytest.mark.asyncio
async def test_delayed_edge2() -> None:
    strat: StrategyAL[int] = StagedStrategy(
        IteratorStrategy([(0.5, SimpleAction(0)), (0.4, SimpleAction(1))]),
        NeverStrategy(),
        prob=0.2,
    )
    actions = await strat.rollout([])
    assert (0.5, [0]) == await next_eval(actions, [])
    assert (0.4, [1]) == await next_eval(actions, [])


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


@pytest.mark.asyncio
@pytest.mark.parametrize("lls, expected", VALUES, ids=[str(x) for _, x in VALUES])
async def test_many(
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
        rollout = await strat.rollout([])
        pairs = await take_all(rollout)
        result = [(prob, (await n.interact([]))[0]) for prob, n in pairs]
        assert result == expected

    for pre_len in range(0, len(result)):
        rollout = await strat.rollout([])
        pairs = await take_n(rollout, pre_len)
        x = [(prob, (await n.interact([]))[0]) for prob, n in pairs]
        assert x == expected[:pre_len]
