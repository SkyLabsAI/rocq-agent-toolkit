from __future__ import annotations

import heapq
import random
from abc import ABC, abstractmethod
from collections.abc import Awaitable, Callable
from dataclasses import dataclass
from typing import Any, Protocol, override, runtime_checkable


@runtime_checkable
class HasId[T](Protocol):
    @property
    def ident(self) -> T: ...


class BasicNode[T](HasId[int]):
    def __init__(self, id: int, state: T) -> None:
        self._id = id
        self._state = state

    @property
    def ident(self) -> int:
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
    # Action metadata is intentionally handled by search-level tracing, not stored in the frontier.
    async def push(self, val: T, parent: Node | None) -> Node:
        """Insert a new item into the frontier"""
        ...

    @abstractmethod
    async def repush(self, node: Node) -> None:
        """Re-add a pulled item back into the frontier.
        This can be used if too many nodes were pulled.
        """
        ...

    @abstractmethod
    async def clear(self) -> None:
        """Remove all pending items from the frontier."""
        ...

    @abstractmethod
    # Remove up to [count] items in frontier order.
    async def take(self, count: int) -> list[tuple[T, Node]]:
        """
        Take up to count nodes from the frontier.
        Returns None if no elements exist
        """
        ...


### == Concrete Implementations ======================================


class DFSNode[U](BasicNode[U]):
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
    async def push(self, val: T, parent: DFSNode[T] | None) -> DFSNode[T]:
        # Prepend to the linked list for LIFO order.
        self._worklist = DFSNode(self._fresh(), self._worklist, val)
        return self._worklist

    @override
    async def repush(self, node: DFSNode[T]) -> None:
        self._worklist = DFSNode(node.ident, self._worklist, node.state)

    @override
    async def clear(self) -> None:
        self._worklist = None

    @override
    async def take(self, count: int) -> list[tuple[T, DFSNode[T]]]:
        if self._worklist is None:
            return []
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
    async def push(self, val: T, parent: BasicNode[T] | None) -> BasicNode[T]:
        # Append for FIFO order.
        node = BasicNode(self._fresh(), val)
        self._worklist.append(node)
        return node

    @override
    async def repush(self, node: BasicNode[T]) -> None:
        self._worklist.append(node)

    @override
    async def clear(self) -> None:
        self._worklist = []

    @override
    async def take(self, count: int) -> list[tuple[T, BasicNode[T]]]:
        if self._worklist:
            # Slice out the next [count] items and retain the rest.
            result = self._worklist[:count]
            self._worklist = self._worklist[count:]
            return [(x.state, x) for x in result]
        return []


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
            return self.ident < other.ident
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
    async def push(self, val: T, parent: Wrapper[T, Any] | None) -> Wrapper[T, Any]:
        # Wrap with score so heapq can order items.
        node = Wrapper(self._fresh(), val, self._score(val), self._compare)
        heapq.heappush(self._worklist, node)
        return node

    @override
    async def repush(self, node: Wrapper[T, Any]) -> None:
        heapq.heappush(self._worklist, node)

    @override
    async def clear(self) -> None:
        self._worklist = []

    @override
    async def take(self, count: int) -> list[tuple[T, Wrapper[T, Any]]]:
        if self._worklist:
            result: list[Wrapper[T, Any]] = []
            while self._worklist and count > 0:
                # test_frontier_pqueue.py: honor count by decrementing per pop.
                # Pop lowest (or highest) priority based on compare.
                result.append(heapq.heappop(self._worklist))
                count -= 1
            return [(x.state, x) for x in result]
        return []


@dataclass
class WithDepth[T: HasId[int]](HasId[int]):
    depth: int
    value: T

    @property
    def ident(self) -> int:
        return self.value.ident


class SingleDepth[T, Node: HasId[int]](Frontier[T, WithDepth[Node]]):
    """
    This class can be used to implement a beam-like search where we take
    once per depth.
    """

    def __init__(self, base: Frontier[tuple[T, int], Node]) -> None:
        self._base = base
        self._max_depth = 0

    @override
    async def take(self, count: int) -> list[tuple[T, WithDepth[Node]]]:
        result = await self._base.take(count)
        return [(state, WithDepth(depth, node)) for ((state, depth), node) in result]

    @override
    async def push(self, val: T, parent: WithDepth[Node] | None) -> WithDepth[Node]:
        depth = parent.depth + 1 if parent is not None else 0
        if depth > self._max_depth:
            await self._base.clear()
            self._max_depth = depth
        node = await self._base.push(
            (val, depth), parent.value if parent is not None else None
        )
        return WithDepth(depth, node)

    @override
    async def repush(self, node: WithDepth[Node]) -> None:
        if node.depth >= self._max_depth:
            await self._base.repush(node.value)

    @override
    async def clear(self) -> None:
        await self._base.clear()
        self._max_depth = 0


class Sampled[T, Node](Frontier[T, Node]):
    """Sample from a broader pull while keeping the remainder in the base."""

    def __init__(self, base: Frontier[T, Node], spread: int = 2) -> None:
        self._base = base
        self._spread = spread

    @override
    async def take(self, count: int) -> list[tuple[T, Node]]:
        pulled = await self._base.take(self._spread * count)
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
                await self._base.repush(v[1])
        return result

    @override
    async def push(self, val: T, parent: Node | None) -> Node:
        return await self._base.push(val, parent)

    @override
    async def repush(self, node: Node) -> None:
        return await self._base.repush(node)

    @override
    async def clear(self) -> None:
        return await self._base.clear()


class Deduplicate[T, Node](Frontier[T, Node]):
    """
    A frontier that de-duplicates states using a comparison function
    """

    def __init__(self, base: Frontier[T, Node], *, cmp: Callable[[T, T], bool]) -> None:
        self._base = base
        # TODO: because we have a total ordering, this should use a balanced binary tree
        self._seen: list[tuple[T, Node]] = []
        self._cmp = cmp

    @override
    async def take(self, count: int) -> list[tuple[T, Node]]:
        return await self._base.take(count)

    @override
    async def repush(self, node: Node) -> None:
        return await self._base.repush(node)

    @override
    async def push(self, val: T, parent: Node | None) -> Node:
        # TODO: A better implementation of this would be to use
        # something like a hash table which would require an embedding
        # into some type.
        for x, n in self._seen:
            if self._cmp(val, x):
                return n
        # test_frontier_deduplicate.py: record unique values before push.
        node = await self._base.push(val, parent)
        self._seen.append((val, node))
        return node

    @override
    async def clear(self) -> None:
        await self._base.clear()
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
        self._seen: dict[U, Node] = {}
        self._key = key

    @override
    async def take(self, count: int) -> list[tuple[T, Node]]:
        return await self._base.take(count)

    @override
    async def repush(self, node: Node) -> None:
        return await self._base.repush(node)

    @override
    async def push(self, val: T, parent: Node | None) -> Node:
        # TODO: A better implementation of this would be to use
        # something like a hash table which would require an embedding
        # into some type.
        key = self._key(val)
        if key in self._seen:
            # test_frontier_deduplicate.py: drop repeats by key.
            # TODO: log message to drop already visited state.
            return self._seen[key]
        # test_frontier_deduplicate.py: record new key before push.
        node = await self._base.push(val, parent)
        self._seen[key] = node
        return node

    @override
    async def clear(self) -> None:
        await self._base.clear()
        self._seen.clear()


class SavingSolutions[T, Node](Frontier[T, Node]):
    """
    A Frontier that tracks solutions.
    """

    def __init__(
        self,
        base: Frontier[T, Node],
        is_solution: Callable[[T], Awaitable[bool]],
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
    async def take(self, count: int) -> list[tuple[T, Node]]:
        if self._stop:
            return []
        return await self._base.take(count)

    @override
    async def push(self, val: T, parent: Node | None) -> Node:
        if await self._check_solution(val):
            self._solutions.append(val)
            self._stop = self._stop or self._stop_on_first_solution

        return await self._base.push(val, parent)

    @override
    async def repush(self, node: Node) -> None:
        if self._stop:
            return
        return await self._base.repush(node)

    @override
    async def clear(self) -> None:
        # Clear cached solutions so a new run does not inherit prior results.
        await self._base.clear()
        self._stop = False
        self._solutions.clear()


class RememberTrace[T, Node](Frontier[T, Node]):
    """
    A Frontier that remebers every node that gets pushed.
    """

    def __init__(
        self,
        base: Frontier[T, Node],
        is_solution: Callable[[T], Awaitable[bool]],
        stop_on_first_solution: bool,
    ) -> None:
        self._base = base
        self._everything: list[tuple[T | None, Node | None]] = []

    def visited_nodes(self) -> list[tuple[T | None, Node | None]]:
        return self._everything

    @override
    async def take(self, count: int) -> list[tuple[T, Node]]:
        return await self._base.take(count)

    @override
    async def push(self, val: T, parent: Node | None) -> Node:
        self._everything.append((val, parent))
        return await self._base.push(val, parent)

    @override
    async def repush(self, node: Node) -> None:
        self._everything.append((None, node))
        return await self._base.repush(node)

    @override
    async def clear(self) -> None:
        # Clear trace history so visited_nodes reflects only the next run.
        await self._base.clear()
        self._everything.clear()
