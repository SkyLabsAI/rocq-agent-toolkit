"""Tests for the Sampled frontier wrapper."""

from __future__ import annotations

import os

import pytest
import rocq_pipeline.search.search.frontier as frontier_module
from rocq_pipeline.search.search.frontier import BFS, Sampled


def _env_int(name: str, default: int) -> int:
    """Read an integer from the environment to keep parameters user-controlled."""
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return int(value)


def _env_int_list(name: str, default: list[int]) -> list[int]:
    """Read a comma-separated integer list from the environment."""
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return [int(item.strip()) for item in value.split(",") if item.strip()]


@pytest.fixture
def sample_values() -> list[int]:
    return _env_int_list("ROCQ_FRONTIER_SAMPLE_VALUES", [1, 2, 3, 4])


@pytest.fixture
def sample_count() -> int:
    return _env_int("ROCQ_FRONTIER_SAMPLE_COUNT", 2)


@pytest.fixture
def sample_spread() -> int:
    return _env_int("ROCQ_FRONTIER_SAMPLE_SPREAD", 2)


@pytest.fixture
def sample_indices(sample_count: int) -> list[int]:
    default = list(range(sample_count))
    return _env_int_list("ROCQ_FRONTIER_SAMPLE_INDEXES", default)


@pytest.mark.asyncio
async def test_sampled_deterministic_sample(
    monkeypatch: pytest.MonkeyPatch,
    sample_values: list[int],
    sample_count: int,
    sample_spread: int,
    sample_indices: list[int],
) -> None:
    """Verify Sampled returns a fixed sample and repushes the remainder. This exercises the sampling branch."""
    if sample_count <= 0:
        pytest.skip("sample_count must be positive for sampling checks.")
    base = BFS[int]()
    for value in sample_values:
        await base.push(value, None)
    frontier = Sampled(base, spread=sample_spread)
    pulled = min(sample_spread * sample_count, len(sample_values))
    if pulled <= sample_count:
        pytest.skip("Need pulled > sample_count to test sampling branch.")
    selected = sorted(set(sample_indices))
    if len(selected) != sample_count or any(i < 0 or i >= pulled for i in selected):
        pytest.skip("sample_indices must be unique and within pulled range.")

    def fixed_sample(_population: range, k: int) -> list[int]:
        assert k == sample_count
        return selected

    monkeypatch.setattr(frontier_module.random, "sample", fixed_sample)

    result = await frontier.take(sample_count)
    assert result is not None
    states = [state for state, _ in result]
    assert states == [sample_values[i] for i in selected]

    remaining = await base.take(len(sample_values))
    remaining_states = [state for state, _ in remaining] if remaining else []
    expected_remaining = sample_values[pulled:] + [
        sample_values[i] for i in range(pulled) if i not in selected
    ]
    assert remaining_states == expected_remaining


@pytest.mark.asyncio
async def test_sampled_small_pull(
    sample_values: list[int], sample_count: int, sample_spread: int
) -> None:
    """Ensure Sampled returns all items when pulled <= count. This exercises the early-return branch."""
    if sample_count <= 0:
        pytest.skip("sample_count must be positive for small pull checks.")
    values = sample_values[:sample_count]
    base = BFS[int]()
    for value in values:
        await base.push(value, None)
    frontier = Sampled(base, spread=sample_spread)
    result = await frontier.take(sample_count)
    assert result is not None
    states = [state for state, _ in result]
    assert states == values
    assert not await base.take(1)
