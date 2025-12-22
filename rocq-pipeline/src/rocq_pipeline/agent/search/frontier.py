from __future__ import annotations

import heapq
import random
from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, override


class Frontier[T](ABC):
    """A collection of values of type `T`."""

    @abstractmethod
    # Insert a new item into the frontier.
    def push(self, val: T) -> None: ...
    @abstractmethod
    # Remove up to [count] items in frontier order.
    def take(self, count: int) -> list[T] | None: ...

    @abstractmethod
    # Clear all pending items in the frontier.
    def clear(self) -> None: ...


class DFS[T](Frontier[T]):
    """Stack-based frontier (depth-first)."""

    @dataclass
    class Node[U]:
        next: DFS.Node | None
        value: U

    def __init__(self) -> None:
        self._worklist: DFS.Node[T] | None = None

    @override
    def push(self, val: T) -> None:
        # Prepend to the linked list for LIFO order.
        self._worklist = DFS.Node(self._worklist, val)

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist is None:
            return None
        result: list[T] = []
        while self._worklist and count > 0:
            if count > 0:
                count -= 1
            # Pop from the head to maintain stack order.
            result.append(self._worklist.value)
            self._worklist = self._worklist.next
        return result

    @override
    def clear(self) -> None:
        # Drop all nodes in the linked list.
        self._worklist = None


class BFS[T](Frontier[T]):
    """Queue-based frontier (breadth-first)."""

    def __init__(self) -> None:
        self._worklist: list[T] = []

    @override
    def push(self, val: T) -> None:
        # Append for FIFO order.
        self._worklist.append(val)

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist:
            # Slice out the next [count] items and retain the rest.
            result = self._worklist[:count]
            self._worklist = self._worklist[count:]
            return result
        return None

    @override
    def clear(self) -> None:
        # Reset queue contents.
        self._worklist = []


class PQueue[T](Frontier[T]):
    """Priority queue frontier with a custom comparator."""

    @dataclass
    class Wrapper[U, V]:
        """Bundle values with scores so heapq can order them."""

        value: U
        score: V
        compare: Callable[[V, V], int]  # this isn't very efficient...

        def __lt__(self, other: PQueue.Wrapper[U, V]) -> bool:
            assert self.compare == other.compare
            return self.compare(self.score, other.score) < 0

    def __init__[U](
        self, score: Callable[[T], U], compare: Callable[[U, U], int]
    ) -> None:
        self._compare: Callable[[Any, Any], Any] = compare
        self._score: Callable[[T], Any] = score
        self._worklist: list[PQueue.Wrapper[T, Any]] = []

    @override
    def push(self, val: T) -> None:
        # Wrap with score so heapq can order items.
        heapq.heappush(
            self._worklist, PQueue.Wrapper(val, self._score(val), self._compare)
        )

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist:
            result = []
            while self._worklist and count > 0:
                # Pop lowest (or highest) priority based on compare.
                result.append(heapq.heappop(self._worklist))
            return result
        return None

    @override
    def clear(self) -> None:
        # Remove all pending elements.
        self._worklist = []


class SingleDepth[T](Frontier[T]):
    """
    This class can be used to implement a beam-like search where we take
    once per depth.
    """

    def __init__(self, base: Frontier[T]) -> None:
        self._base = base

    @override
    def take(self, count: int) -> list[T] | None:
        result = self._base.take(count)
        # once we take, we clear the underlying frontier so that all values
        # in `self._base` will be at the same depth.
        self._base.clear()
        return result

    def push(self, val: T) -> None:
        return self._base.push(val)

    def clear(self) -> None:
        return self._base.clear()


class Sampled[T](Frontier[T]):
    """Sample from a broader pull while keeping the remainder in the base."""

    def __init__(self, base: Frontier[T], spread: int = 2) -> None:
        self._base = base
        self._spread = spread

    @override
    def take(self, count: int) -> list[T] | None:
        pulled = self._base.take(self._spread * count)
        if pulled is None:
            return None
        num_pulled = len(pulled)
        if num_pulled <= count:
            return pulled
        # Sample a subset and push back the remainder.
        indexes = random.sample(range(0, num_pulled), count)
        result = []
        for i, v in enumerate(pulled):
            if i in indexes:
                result.append(v)
            else:
                self._base.push(v)
        return result

    @override
    def push(self, val: T) -> None:
        return self._base.push(val)

    @override
    def clear(self) -> None:
        return self._base.clear()
