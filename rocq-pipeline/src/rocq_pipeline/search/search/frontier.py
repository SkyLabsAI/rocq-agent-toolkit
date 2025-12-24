from __future__ import annotations

import heapq
import random
from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, override


class BasicNode[T]:  # (HasId[int]):
    def __init__(self, id: int, state: T) -> None:
        self._id = id
        self._state = state

    @property
    def id(self) -> int:
        return self._id

    @property
    def state(self) -> T:
        return self._state


class Frontier[T, Node](ABC):
    """
    A collection of values of type `T`.

    The type `N` would normally be implemented as a nested type.
    """

    @abstractmethod
    def push(self, val: T, parent: Node | None) -> None:
        """Insert a new item into the frontier"""
        ...

    @abstractmethod
    def repush(self, node: Node) -> None:
        """Re-add a pulled item back into the frontier.
        This can be used if too many nodes were pulled.
        """
        ...

    @abstractmethod
    def clear(self) -> None:
        """Remove all pending items from the frontier."""
        ...

    @abstractmethod
    # Remove up to [count] items in frontier order.
    def take(self, count: int) -> list[tuple[T, Node]] | None:
        """
        Take up to count nodes from the frontier.
        Returns None if no elements exist
        """
        ...


### == Concrete Implementations ======================================


class DFSNode[U](BasicNode):
    next: DFSNode | None

    def __init__(self, id: int, next: DFSNode | None, value: U) -> None:
        super().__init__(id, value)
        self.next = next


class DFS[T](Frontier[T, DFSNode[T]]):
    """Stack-based frontier (depth-first)."""

    def __init__(self) -> None:
        self._worklist: DFSNode[T] | None = None
        self._next = 0

    def _fresh(self) -> int:
        self._next += 1
        return self._next

    @override
    def push(self, val: T, parent: DFSNode[T] | None) -> None:
        # Prepend to the linked list for LIFO order.
        self._worklist = DFSNode(self._fresh(), self._worklist, val)

    @override
    def repush(self, node: DFSNode[T]) -> None:
        self._worklist = DFSNode(node.id, self._worklist, node.state)

    @override
    def clear(self) -> None:
        self._worklist = None

    @override
    def take(self, count: int) -> list[tuple[T, DFSNode[T]]] | None:
        if self._worklist is None:
            return None
        result: list[tuple[T, DFSNode[T]]] = []
        while self._worklist and count > 0:
            if count > 0:
                count -= 1
            # Pop from the head to maintain stack order.
            result.append((self._worklist.state, self._worklist))
            self._worklist = self._worklist.next
        return result


class BFS[T](Frontier[T, BasicNode[T]]):
    """Queue-based frontier (breadth-first)."""

    def __init__(self) -> None:
        self._worklist: list[BasicNode[T]] = []
        self._next = 0

    def _fresh(self) -> int:
        self._next += 1
        return self._next

    @override
    def push(self, val: T, parent: BasicNode | None) -> None:
        # Append for FIFO order.
        self._worklist.append(BasicNode(self._fresh(), val))

    @override
    def repush(self, node: BasicNode[T]) -> None:
        self._worklist.append(node)

    @override
    def clear(self) -> None:
        self._worklist = []

    @override
    def take(self, count: int) -> list[tuple[T, BasicNode]] | None:
        if self._worklist:
            # Slice out the next [count] items and retain the rest.
            result = self._worklist[:count]
            self._worklist = self._worklist[count:]
            return [(x.state, x) for x in result]
        return None


class Wrapper[T, V](BasicNode[T]):
    """Bundle values with scores so heapq can order them."""

    def __init__(
        self, id: int, state: T, score: V, compare: Callable[[V, V], int]
    ) -> None:
        super().__init__(id, state)
        self._score = score
        self._compare = compare

    def __lt__(self, other: Wrapper[T, V]) -> bool:
        assert self._compare == other._compare
        cmp = self._compare(self._score, other._score)
        if cmp == 0:
            return self.id < other.id
        else:
            return cmp < 0


class PQueue[T](Frontier[T, Wrapper[T, Any]]):
    """Priority queue frontier with a custom comparator."""

    def __init__[U](
        self, score: Callable[[T], U], compare: Callable[[U, U], int]
    ) -> None:
        self._compare: Callable[[Any, Any], Any] = compare
        self._score: Callable[[T], Any] = score
        self._worklist: list[Wrapper[T, Any]] = []
        self._next: int = 0

    def _fresh(self) -> int:
        self._next += 1
        return self._next

    @override
    def push(self, val: T, parent: Wrapper[T, Any] | None) -> None:
        # Wrap with score so heapq can order items.
        heapq.heappush(
            self._worklist, Wrapper(self._fresh(), val, self._score(val), self._compare)
        )

    @override
    def repush(self, node: Wrapper[T, Any]) -> None:
        heapq.heappush(self._worklist, node)

    @override
    def clear(self) -> None:
        self._worklist = []

    @override
    def take(self, count: int) -> list[tuple[T, Wrapper[T, Any]]] | None:
        if self._worklist:
            result: list[Wrapper[T, Any]] = []
            while self._worklist and count > 0:
                # Pop lowest (or highest) priority based on compare.
                result.append(heapq.heappop(self._worklist))
            return [(x.state, x) for x in result]
        return None


@dataclass
class WithDepth[T]:
    depth: int
    value: T


class SingleDepth[T, Node](Frontier[T, WithDepth[Node]]):
    """
    This class can be used to implement a beam-like search where we take
    once per depth.
    """

    def __init__(self, base: Frontier[tuple[T, int], Node]) -> None:
        self._base = base
        self._max_depth = 0

    @override
    def take(self, count: int) -> list[tuple[T, WithDepth[Node]]] | None:
        result = self._base.take(count)
        if result is None:
            return result
        return [(state, WithDepth(depth, node)) for ((state, depth), node) in result]

    @override
    def push(self, val: T, parent: WithDepth[Node] | None) -> None:
        depth = parent.depth + 1 if parent is not None else 0
        if depth > self._max_depth:
            self._base.clear()
            self._max_depth = depth
        self._base.push((val, depth), parent.value if parent is not None else None)

    @override
    def repush(self, node: WithDepth[Node]) -> None:
        self._base.repush(node.value)

    @override
    def clear(self) -> None:
        self._base.clear()
        self._max_depth = 0


class Sampled[T, Node](Frontier[T, Node]):
    """Sample from a broader pull while keeping the remainder in the base."""

    def __init__(self, base: Frontier[T, Node], spread: int = 2) -> None:
        self._base = base
        self._spread = spread

    @override
    def take(self, count: int) -> list[tuple[T, Node]] | None:
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
                self._base.repush(v[1])
        return result

    @override
    def push(self, val: T, parent: Node | None) -> None:
        return self._base.push(val, parent)

    @override
    def repush(self, node: Node) -> None:
        return self._base.repush(node)

    @override
    def clear(self) -> None:
        return self._base.clear()


class Deduplicate[T, Node](Frontier[T, Node]):
    """
    A frontier that de-duplicates states using a comparison function
    """

    def __init__(self, base: Frontier[T, Node], *, cmp: Callable[[T, T], bool]) -> None:
        self._base = base
        # TODO: because we have a total ordering, this should use a balanced binary tree
        self._seen: list[T] = []
        self._cmp = cmp

    @override
    def take(self, count: int) -> list[tuple[T, Node]] | None:
        return self._base.take(count)

    @override
    def repush(self, node: Node) -> None:
        return self._base.repush(node)

    @override
    def push(self, val: T, parent: Node | None) -> None:
        # TODO: A better implementation of this would be to use
        # something like a hash table which would require an embedding
        # into some type.
        if any(True for x in self._seen if self._cmp(val, x)):
            # TODO: log message to drop already visited state
            return self._base.push(val, parent)

    @override
    def clear(self) -> None:
        self._base.clear()
        self._seen.clear()


class DeduplicateWithKey[T, Node, U](Frontier[T, Node]):
    """
    A frontier that de-duplicates states based on a key function.
    The key function should return the same value on two state if and only if
    those two states should be considered equivalent.

    This is more efficient than `Deduplicate`.
    """

    def __init__(self, base: Frontier[T, Node], *, key: Callable[[T], U]) -> None:
        self._base = base
        self._seen: set[U] = set()
        self._key = key

    @override
    def take(self, count: int) -> list[tuple[T, Node]] | None:
        return self._base.take(count)

    @override
    def repush(self, node: Node) -> None:
        return self._base.repush(node)

    @override
    def push(self, val: T, parent: Node | None) -> None:
        # TODO: A better implementation of this would be to use
        # something like a hash table which would require an embedding
        # into some type.
        if self._key(val) not in self._seen:
            # TODO: log message to drop already visited state
            return self._base.push(val, parent)

    @override
    def clear(self) -> None:
        self._base.clear()
        self._seen.clear()


class SavingSolutions[T, Node](Frontier[T, Node]):
    """
    A Frontier that tracks solutions.
    """

    def __init__(
        self,
        base: Frontier[T, Node],
        is_solution: Callable[[T], bool],
        stop_on_first_solution: bool,
    ) -> None:
        self._base = base
        self._check_solution = is_solution
        self._stop_on_first_solution = stop_on_first_solution
        self._stop = False
        self._solutions: list[T] = []

    def solutions(self) -> list[T]:
        return self._solutions

    @override
    def take(self, count: int) -> list[tuple[T, Node]] | None:
        if self._stop:
            return None
        return self._base.take(count)

    @override
    def push(self, val: T, parent: Node | None) -> None:
        if self._check_solution(val):
            self._solutions.append(val)
            self._stop = self._stop or self._stop_on_first_solution

        if self._stop:
            return
        self._base.push(val, parent)

    @override
    def repush(self, node: Node) -> None:
        if self._stop:
            return
        return self._base.repush(node)

    @override
    def clear(self) -> None:
        self._base.clear()
        self._stop = False


class RememberTrace[T, Node](Frontier[T, Node]):
    """
    A Frontier that remebers every node that gets pushed.
    """

    def __init__(
        self,
        base: Frontier[T, Node],
        is_solution: Callable[[T], bool],
        stop_on_first_solution: bool,
    ) -> None:
        self._base = base
        self._everything: list[tuple[T | None, Node | None]] = []

    def visited_nodes(self) -> list[tuple[T | None, Node | None]]:
        return self._everything

    @override
    def take(self, count: int) -> list[tuple[T, Node]] | None:
        return self._base.take(count)

    @override
    def push(self, val: T, parent: Node | None) -> None:
        self._everything.append((val, parent))
        return self._base.push(val, parent)

    @override
    def repush(self, node: Node) -> None:
        self._everything.append((None, node))
        return self._base.repush(node)

    @override
    def clear(self) -> None:
        self._base.clear()
