import pytest
from rocq_pipeline.search.rollout import (
    DeduplicateRollout,
    IteratorRollout,
    Rollout,
    empty_Rollout,
    singleton,
)

from .rollout_util import is_empty


@pytest.mark.asyncio
async def test_empty() -> None:
    rollout: Rollout[int] = DeduplicateRollout(empty_Rollout())

    await is_empty(rollout)


@pytest.mark.asyncio
async def test_singleton() -> None:
    rollout: Rollout[int] = DeduplicateRollout(singleton(1, score=-1.0))

    assert [x async for x in rollout] == [(-1, 1)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_multiple() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.5, 2), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.5, 2), (0.25, 3)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_duplicate() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.5, 1), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.25, 3)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_duplicate2() -> None:
    rollout: Rollout[int] = DeduplicateRollout(
        IteratorRollout(iter([(1, 1), (0.75, 1), (0.5, 1), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.25, 3)]
    await is_empty(rollout)
