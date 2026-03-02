import pytest
from pyroof_search.rollout import (
    DeduplicateRollout,
    Proposals,
    empty,
    from_iterator,
    singleton,
)

from .rollout_util import is_empty


@pytest.mark.asyncio
async def test_empty() -> None:
    rollout: Proposals[int] = DeduplicateRollout(empty())

    await is_empty(rollout)


@pytest.mark.asyncio
async def test_singleton() -> None:
    rollout: Proposals[int] = DeduplicateRollout(singleton(1, score=-1.0))

    assert [x async for x in rollout] == [(-1, 1)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_multiple() -> None:
    rollout: Proposals[int] = DeduplicateRollout(
        from_iterator(iter([(1, 1), (0.5, 2), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.5, 2), (0.25, 3)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_duplicate() -> None:
    rollout: Proposals[int] = DeduplicateRollout(
        from_iterator(iter([(1, 1), (0.5, 1), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.25, 3)]
    await is_empty(rollout)


@pytest.mark.asyncio
async def test_duplicate2() -> None:
    rollout: Proposals[int] = DeduplicateRollout(
        from_iterator(iter([(1, 1), (0.75, 1), (0.5, 1), (0.25, 3)]))
    )

    assert [x async for x in rollout] == [(1, 1), (0.25, 3)]
    await is_empty(rollout)
