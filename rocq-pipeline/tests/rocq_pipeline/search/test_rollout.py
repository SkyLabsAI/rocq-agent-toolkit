from collections.abc import Generator
from math import log

from rocq_pipeline.search.rollout import (
    InterleaveRollout,
    IteratorRollout,
    Rollout,
    SingletonRollout,
)


def is_empty[T](r: Rollout[T]) -> None:
    try:
        result = r.next()
        raise AssertionError(f"Should be empty, but got {result}")
    except StopIteration:
        pass


def test_interleave_empty() -> None:
    ch: list[Rollout[int]] = []
    ir = InterleaveRollout(ch)

    is_empty(ir)


def approx[T](logprob: float, result: T | None) -> Rollout.Approx[T]:
    return Rollout.Approx(logprob=logprob, result=result)


def test_interleave_delayed() -> None:
    def tester() -> Generator[Rollout.Approx[int]]:
        yield approx(logprob=log(0.3), result=None)
        raise AssertionError("Should not force value")

    ch: list[Rollout[int]] = [
        SingletonRollout(1, logprob=log(0.5)),
        IteratorRollout(tester()),
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
        SingletonRollout(1, logprob=log(0.1)),
    ]
    ir = InterleaveRollout(ch)

    assert ir.next(log(0.5)) == approx(log(0.1), None)
    assert ir.next(log(0.6)) == approx(log(0.1), None)
    assert ir.next(log(0.1)) == approx(log(0.1), 1)
    is_empty(ir)


def test_interleave_rollout() -> None:
    ch: list[Rollout[int]] = [
        SingletonRollout(1, logprob=log(0.1)),
        SingletonRollout(2, logprob=log(0.2)),
    ]
    ir = InterleaveRollout(ch)

    assert ir.next(log(0.5)) == approx(log(0.2), None)
    assert ir.next(log(0.6)) == approx(log(0.2), None)
    assert ir.next(log(0.2)) == approx(log(0.2), 2)
    assert ir.next(log(0.2)) == approx(log(0.1), None)
    assert ir.next(log(0.1)) == approx(log(0.1), 1)
    is_empty(ir)
