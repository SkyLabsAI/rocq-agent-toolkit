from rocq_pipeline.search.rollout import (
    DeduplicateRollout,
    IteratorRollout,
    Rollout,
    empty_Rollout,
    singleton,
)

from .rollout_util import is_empty


def test_empty() -> None:
    rollout: Rollout[int] = DeduplicateRollout(empty_Rollout())

    is_empty(rollout)


def test_singleton() -> None:
    rollout: Rollout[int] = DeduplicateRollout(singleton(1, score=-1.0))

    assert list(rollout) == [(-1, 1)]
    is_empty(rollout)


def test_multiple() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.5, 2), (0.25, 3)]))
    )

    assert list(rollout) == [(1, 1), (0.5, 2), (0.25, 3)]
    is_empty(rollout)


def test_duplicate() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.5, 1), (0.25, 3)]))
    )

    assert list(rollout) == [(1, 1), (0.25, 3)]
    is_empty(rollout)


def test_duplicate2() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.75, 1), (0.5, 1), (0.25, 3)]))
    )

    assert list(rollout) == [(1, 1), (0.25, 3)]
    is_empty(rollout)
