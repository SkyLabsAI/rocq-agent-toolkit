from __future__ import annotations

from pyroof_search.search.iter import Interleaver, RolloutInterleaver


def is_empty[K, T](i: Interleaver[K, T]) -> None:
    try:
        elem = next(i)
        raise AssertionError(f"empty contains element {elem}")
    except StopIteration:
        pass


def test_empty() -> None:
    i: Interleaver[int, int] = Interleaver({})
    is_empty(i)
    assert not i.stop()


def test_empty_1() -> None:
    i: Interleaver[int, int] = Interleaver({1: iter([])})
    is_empty(i)
    assert len(i.stop().keys()) == 0


def test_nonempty_1() -> None:
    i = Interleaver({1: iter([9])})

    assert (1, 9) == next(i)
    is_empty(i)


def test_nonempty_2() -> None:
    i = Interleaver({1: iter([9, 8])})

    assert (1, 9) == next(i)
    assert (1, 8) == next(i)
    is_empty(i)


def test_nonempty_3() -> None:
    i = Interleaver({1: iter([9, 8]), 2: iter([3, 4])})

    assert (2, 3) == next(i)
    assert (2, 4) == next(i)
    assert (1, 9) == next(i)
    assert (1, 8) == next(i)
    is_empty(i)


def test_nonempty_4() -> None:
    i = Interleaver({1: iter([2, 8]), 2: iter([3, 4])})

    assert (1, 2) == next(i)
    assert (2, 3) == next(i)
    assert (2, 4) == next(i)
    assert (1, 8) == next(i)
    is_empty(i)


class NonComparable[T]:
    def __init__(self, value: T) -> None:
        self.value = value

    def __lt__(self, other: NonComparable[T]) -> bool:
        raise AssertionError("Comparing NonComparable values")


def test_non_comparable() -> None:
    i = RolloutInterleaver(
        {
            1: iter([(0.75, NonComparable(x)) for x in [2, 8]]),
            2: iter([(0.75, NonComparable(x)) for x in [3, 4]]),
        }
    )

    def value_is(who: int, prob: float, val: int) -> None:
        nonlocal i
        obs_who, (obs_prob, obs_val) = next(i)
        assert who == obs_who
        assert prob == obs_prob
        assert val == obs_val.value

    value_is(1, 0.75, 2)
    value_is(1, 0.75, 8)
    value_is(2, 0.75, 3)
    value_is(2, 0.75, 4)


def test_non_comparable2() -> None:
    i = RolloutInterleaver(
        {
            1: iter([(prob, NonComparable(x)) for prob, x in [(0.75, 2), (0.65, 8)]]),
            2: iter([(prob, NonComparable(x)) for prob, x in [(0.85, 3), (0.7, 4)]]),
        }
    )

    def value_is(who: int, prob: float, val: int) -> None:
        nonlocal i
        obs_who, (obs_prob, obs_val) = next(i)
        assert who == obs_who
        assert prob == obs_prob
        assert val == obs_val.value

    value_is(2, 0.85, 3)
    value_is(1, 0.75, 2)
    value_is(2, 0.7, 4)
    value_is(1, 0.65, 8)
