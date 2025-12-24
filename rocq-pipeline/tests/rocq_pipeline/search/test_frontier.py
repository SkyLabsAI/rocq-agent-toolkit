"""Tests for frontier behaviors and wrappers."""

from __future__ import annotations

import os

import pytest

import rocq_pipeline.search.search.frontier as frontier_module
from rocq_pipeline.search.search.frontier import (
    BFS,
    DFS,
    BasicNode,
    Deduplicate,
    DeduplicateWithKey,
    PQueue,
    RememberTrace,
    Sampled,
    SavingSolutions,
    SingleDepth,
    WithDepth,
)


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


def _numeric_compare(a: int, b: int) -> int:
    """Three-way comparator for priority queue ordering."""
    return (a > b) - (a < b)


@pytest.fixture
def take_count() -> int:
    return _env_int("ROCQ_FRONTIER_TAKE_COUNT", 2)


@pytest.fixture
def push_values() -> list[int]:
    return _env_int_list("ROCQ_FRONTIER_PUSH_VALUES", [1, 2, 3])


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


def test_take_empty_returns_none() -> None:
    """Ensure empty frontiers return None on take. This matches the search loop termination contract."""
    assert DFS[int]().take(1) is None
    assert BFS[int]().take(1) is None


def test_dfs_ordering(push_values: list[int], take_count: int) -> None:
    """Verify DFS returns values in LIFO order. This checks stack behavior for depth-first search."""
    if take_count <= 0:
        pytest.skip("take_count must be positive for ordering checks.")
    assert len(push_values) >= 2
    frontier = DFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == list(reversed(push_values))[:take_count]


def test_bfs_ordering(push_values: list[int], take_count: int) -> None:
    """Verify BFS returns values in FIFO order. This checks queue behavior for breadth-first search."""
    if take_count <= 0:
        pytest.skip("take_count must be positive for ordering checks.")
    assert len(push_values) >= 2
    frontier = BFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == push_values[:take_count]


def test_dfs_repush_front(push_values: list[int]) -> None:
    """Ensure DFS repush restores the node to the front. This preserves LIFO expansion after partial pulls."""
    assert len(push_values) >= 2
    frontier = DFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(1)
    assert taken is not None
    state, node = taken[0]
    frontier.repush(node)
    next_take = frontier.take(1)
    assert next_take is not None
    assert next_take[0][0] == state


def test_bfs_repush_appends(push_values: list[int]) -> None:
    """Ensure BFS repush appends the node to the back. This preserves FIFO expansion after partial pulls."""
    assert len(push_values) >= 2
    frontier = BFS[int]()
    for value in push_values:
        frontier.push(value, None)
    first = frontier.take(1)
    assert first is not None
    state, node = first[0]
    frontier.repush(node)
    rest = frontier.take(len(push_values))
    assert rest is not None
    states = [value for value, _ in rest]
    assert states == push_values[1:] + [state]


def test_pqueue_priority_ordering(push_values: list[int]) -> None:
    """Verify PQueue returns states ordered by score. Lower scores should come out first for the comparator."""
    frontier = PQueue(score=lambda v: v, compare=_numeric_compare)
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(len(push_values))
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == sorted(push_values)


def test_pqueue_tiebreaks_by_id() -> None:
    """Verify PQueue ties break by insertion id. This keeps ordering deterministic when scores match."""
    frontier = PQueue(score=lambda _: 0, compare=_numeric_compare)
    frontier.push("first", None)
    frontier.push("second", None)
    taken = frontier.take(2)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == ["first", "second"]


def test_pqueue_respects_count(push_values: list[int], take_count: int) -> None:
    """Ensure PQueue take respects count limits. The frontier should not drain more than requested."""
    if take_count <= 0 or take_count >= len(push_values):
        pytest.skip("Need 0 < take_count < len(push_values) to test count handling.")
    frontier = PQueue(score=lambda v: v, compare=_numeric_compare)
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    assert len(taken) == take_count


def test_single_depth_take_wraps_depth() -> None:
    """Verify SingleDepth wraps nodes with depth metadata. This is required for beam-style depth tracking."""
    base = BFS[tuple[str, int]]()
    frontier = SingleDepth(base)
    frontier.push("alpha", None)
    taken = frontier.take(1)
    assert taken is not None
    state, node = taken[0]
    assert state == "alpha"
    assert isinstance(node, WithDepth)
    assert node.depth == 0
    assert node.value.state == ("alpha", 0)


def test_single_depth_clears_on_deeper_push() -> None:
    """Ensure SingleDepth clears the base on depth increases. This enforces single-depth expansion semantics."""
    base = BFS[tuple[str, int]]()
    frontier = SingleDepth(base)
    frontier.push("first", None)
    frontier.push("second", None)
    parent = WithDepth(depth=0, value=BasicNode(1, ("seed", 0)))
    frontier.push("third", parent)
    remaining = base.take(10)
    assert remaining is not None
    states = [state for state, _ in remaining]
    assert states == [("third", 1)]


def test_single_depth_repush_delegates() -> None:
    """Verify SingleDepth repush delegates to its base frontier. The wrapper should not alter repush ordering."""
    base = BFS[tuple[str, int]]()
    frontier = SingleDepth(base)
    node = BasicNode(7, ("seed", 2))
    frontier.repush(WithDepth(depth=2, value=node))
    taken = base.take(1)
    assert taken is not None
    assert taken[0][0] == ("seed", 2)


def test_sampled_deterministic_sample(
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
        base.push(value, None)
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

    result = frontier.take(sample_count)
    assert result is not None
    states = [state for state, _ in result]
    assert states == [sample_values[i] for i in selected]

    remaining = base.take(len(sample_values))
    remaining_states = [state for state, _ in remaining] if remaining else []
    expected_remaining = sample_values[pulled:] + [
        sample_values[i] for i in range(pulled) if i not in selected
    ]
    assert remaining_states == expected_remaining


def test_sampled_small_pull(
    sample_values: list[int], sample_count: int, sample_spread: int
) -> None:
    """Ensure Sampled returns all items when pulled <= count. This exercises the early-return branch."""
    if sample_count <= 0:
        pytest.skip("sample_count must be positive for small pull checks.")
    values = sample_values[:sample_count]
    base = BFS[int]()
    for value in values:
        base.push(value, None)
    frontier = Sampled(base, spread=sample_spread)
    result = frontier.take(sample_count)
    assert result is not None
    states = [state for state, _ in result]
    assert states == values
    assert base.take(1) is None


def test_deduplicate_drops_duplicates() -> None:
    """Verify Deduplicate drops equivalent states. Only the first instance should be queued."""
    base = BFS[int]()
    frontier = Deduplicate(base, cmp=lambda a, b: a == b)
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(1, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2]


def test_deduplicate_clear_resets() -> None:
    """Ensure Deduplicate clear resets the seen state. A fresh run should accept prior values."""
    base = BFS[int]()
    frontier = Deduplicate(base, cmp=lambda a, b: a == b)
    frontier.push(1, None)
    frontier.clear()
    frontier.push(1, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]


def test_deduplicate_key_drops_duplicates() -> None:
    """Verify DeduplicateWithKey drops states with the same key. Keys define equivalence, not identity."""
    base = BFS[int]()
    frontier = DeduplicateWithKey(base, key=lambda v: v % 2)
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(3, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2]


def test_deduplicate_key_clear_resets() -> None:
    """Ensure DeduplicateWithKey clear resets the seen keys. A fresh run should accept prior keys."""
    base = BFS[int]()
    frontier = DeduplicateWithKey(base, key=lambda v: v % 2)
    frontier.push(1, None)
    frontier.clear()
    frontier.push(1, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]


def test_saving_solutions_capture() -> None:
    """Verify SavingSolutions captures solutions without stopping. This is intended when stop_on_first_solution is False."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v % 2 == 0,
        stop_on_first_solution=False,
    )
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(4, None)
    assert frontier.solutions() == [2, 4]
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2, 4]


def test_saving_solutions_stop_on_first() -> None:
    """Verify SavingSolutions stops after the first solution. This is intended when stop_on_first_solution is True."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v == 2,
        stop_on_first_solution=True,
    )
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(3, None)
    assert frontier.solutions() == [2]
    assert frontier.take(1) is None
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]


def test_saving_solutions_clear_resets() -> None:
    """Ensure SavingSolutions clear resets stop state and solutions. A fresh run should not inherit prior results."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v == 1,
        stop_on_first_solution=True,
    )
    frontier.push(1, None)
    assert frontier.solutions() == [1]
    frontier.clear()
    assert frontier.solutions() == []
    frontier.push(2, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [2]


def test_remember_trace_push_and_repush() -> None:
    """Verify RememberTrace records push and repush entries. Repush entries should be tagged with None values."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=lambda _: False,
        stop_on_first_solution=False,
    )
    parent = BasicNode(1, 99)
    frontier.push(1, parent)
    node = BasicNode(2, 2)
    frontier.repush(node)
    assert frontier.visited_nodes() == [(1, parent), (None, node)]


def test_remember_trace_clear_resets() -> None:
    """Ensure RememberTrace clear resets the trace history. A fresh run should not include prior visits."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=lambda _: False,
        stop_on_first_solution=False,
    )
    frontier.push(1, None)
    frontier.clear()
    assert frontier.visited_nodes() == []
