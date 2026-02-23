from collections.abc import Generator
from math import log

import pytest
from pyroof_search.rollout import (
    ApproximatingRollout,
    InterleaveRollout,
    Rollout,
    singleton,
)

from .rollout_util import approx, is_empty


@pytest.mark.asyncio
async def test_interleave_empty() -> None:
    ch: list[Rollout[int]] = []
    ir = InterleaveRollout(ch)

    await is_empty(ir)


@pytest.mark.asyncio
async def test_interleave_delayed() -> None:
    def tester() -> Generator[Rollout.Approx[int]]:
        yield approx(logprob=log(0.3), result=None)
        raise AssertionError("Should not force value")

    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.5)),
        ApproximatingRollout(tester()),
    ]
    ir = InterleaveRollout(ch)

    assert (await ir.next(log(0.6))) == approx(logprob=log(0.5), result=None)
    assert (await ir.next(log(0.5))) == approx(logprob=log(0.5), result=1)
    # this demonstrates that the assertion does not fire
    await ir.next(log(0.31))
    await ir.next(log(0.31))
    try:
        await ir.next(log(0.3))
    except AssertionError:
        pass


@pytest.mark.asyncio
async def test_interleave_1() -> None:
    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.1)),
    ]
    ir = InterleaveRollout(ch)

    assert await ir.next(log(0.5)) == approx(log(0.1), None)
    assert await ir.next(log(0.6)) == approx(log(0.1), None)
    assert await ir.next(log(0.1)) == approx(log(0.1), 1)
    await is_empty(ir)


@pytest.mark.asyncio
async def test_interleave_rollout() -> None:
    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.1)),
        singleton(2, score=log(0.2)),
    ]
    ir = InterleaveRollout(ch)

    assert await ir.next(log(0.5)) == approx(log(0.2), None)
    assert await ir.next(log(0.6)) == approx(log(0.2), None)
    assert await ir.next(log(0.2)) == approx(log(0.2), 2)
    assert await ir.next(log(0.2)) == approx(log(0.1), None)
    assert await ir.next(log(0.1)) == approx(log(0.1), 1)
    await is_empty(ir)


@pytest.mark.parametrize("value", [1, 2])
@pytest.mark.parametrize("score", [float("inf"), 1, 0, -1, -float("inf")])
@pytest.mark.parametrize("probe", [float("inf"), 1, 0, -1, -float("inf")])
@pytest.mark.asyncio
async def test_singleton(value: int, score: float, probe: float) -> None:
    r = singleton(value, score=score)
    if score >= probe:
        assert await r.next(probe) == Rollout.Approx(logprob=score, result=value)
        await is_empty(r)
    else:
        assert await r.next(probe) == Rollout.Approx(logprob=score, result=None)
