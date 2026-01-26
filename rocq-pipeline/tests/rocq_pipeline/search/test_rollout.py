from collections.abc import Generator
from math import log

import pytest
from rocq_pipeline.search.rollout import (
    ApproximatingRollout,
    InterleaveRollout,
    Rollout,
    singleton,
)

from .rollout_util import approx, is_empty


def test_interleave_empty() -> None:
    ch: list[Rollout[int]] = []
    ir = InterleaveRollout(ch)

    is_empty(ir)


def test_interleave_delayed() -> None:
    def tester() -> Generator[Rollout.Approx[int]]:
        yield approx(logprob=log(0.3), result=None)
        raise AssertionError("Should not force value")

    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.5)),
        ApproximatingRollout(tester()),
    ]
    ir = InterleaveRollout(ch)

    assert ir.next(log(0.6)) == approx(logprob=log(0.5), result=None)
    assert ir.next(log(0.5)) == approx(logprob=log(0.5), result=1)
    # this demonstrates that the assertion does not fire
    ir.next(log(0.31))
    ir.next(log(0.31))
    try:
        ir.next(log(0.3))
    except AssertionError:
        pass


def test_interleave_1() -> None:
    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.1)),
    ]
    ir = InterleaveRollout(ch)

    assert ir.next(log(0.5)) == approx(log(0.1), None)
    assert ir.next(log(0.6)) == approx(log(0.1), None)
    assert ir.next(log(0.1)) == approx(log(0.1), 1)
    is_empty(ir)


def test_interleave_rollout() -> None:
    ch: list[Rollout[int]] = [
        singleton(1, score=log(0.1)),
        singleton(2, score=log(0.2)),
    ]
    ir = InterleaveRollout(ch)

    assert ir.next(log(0.5)) == approx(log(0.2), None)
    assert ir.next(log(0.6)) == approx(log(0.2), None)
    assert ir.next(log(0.2)) == approx(log(0.2), 2)
    assert ir.next(log(0.2)) == approx(log(0.1), None)
    assert ir.next(log(0.1)) == approx(log(0.1), 1)
    is_empty(ir)


@pytest.mark.parametrize("value", [1, 2])
@pytest.mark.parametrize("score", [float("inf"), 1, 0, -1, -float("inf")])
@pytest.mark.parametrize("probe", [float("inf"), 1, 0, -1, -float("inf")])
def test_singleton(value: int, score: float, probe: float) -> None:
    r = singleton(value, score=score)
    if score >= probe:
        assert r.next(probe) == Rollout.Approx(logprob=score, result=value)
        is_empty(r)
    else:
        assert r.next(probe) == Rollout.Approx(logprob=score, result=None)
