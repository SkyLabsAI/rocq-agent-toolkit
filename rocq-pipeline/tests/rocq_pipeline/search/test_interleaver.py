from rocq_pipeline.search.search.search import Interleaver


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
