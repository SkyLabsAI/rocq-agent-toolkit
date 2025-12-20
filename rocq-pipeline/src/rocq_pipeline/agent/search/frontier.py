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
    def push(self, val: T) -> None: ...
    @abstractmethod
    def take(self, count: int) -> list[T] | None: ...

    @abstractmethod
    def clear(self) -> None: ...


class DFS[T](Frontier[T]):
    @dataclass
    class Node[U]:
        next: DFS.Node | None
        value: U

    def __init__(self) -> None:
        self._worklist: DFS.Node[T] | None = None

    @override
    def push(self, val: T) -> None:
        self._worklist = DFS.Node(self._worklist, val)

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist is None:
            return None
        result: list[T] = []
        while self._worklist and count > 0:
            if count > 0:
                count -= 1
            result.append(self._worklist.value)
            self._worklist = self._worklist.next
        return result

    @override
    def clear(self) -> None:
        self._worklist = None


class BFS[T](Frontier[T]):
    def __init__(self) -> None:
        self._worklist: list[T] = []

    @override
    def push(self, val: T) -> None:
        self._worklist.append(val)

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist:
            result = self._worklist[:count]
            self._worklist = self._worklist[count:]
            return result
        return None

    @override
    def clear(self) -> None:
        self._worklist = []


class PQueue[T](Frontier[T]):
    @dataclass
    class Wrapper[U, V]:
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
        heapq.heappush(
            self._worklist, PQueue.Wrapper(val, self._score(val), self._compare)
        )

    @override
    def take(self, count: int) -> list[T] | None:
        if self._worklist:
            result = []
            while self._worklist and count > 0:
                result.append(heapq.heappop(self._worklist))
            return result
        return None

    @override
    def clear(self) -> None:
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
