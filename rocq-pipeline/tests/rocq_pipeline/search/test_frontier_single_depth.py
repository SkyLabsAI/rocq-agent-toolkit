"""Tests for the SingleDepth frontier."""

from __future__ import annotations

from rocq_pipeline.search.search.frontier import BFS, BasicNode, SingleDepth, WithDepth


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
