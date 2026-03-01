from __future__ import annotations

import heapq
from collections.abc import Iterator


class Interleaver[K, T]:
    """
    Interleaves multiple generators and provides a `stop` method to
    get the remaining generators back.
    """

    def __init__(self, mp: dict[K, Iterator[T]]) -> None:
        self._gens = mp
        self._waiting: list[tuple[T, K]] = []
        self._done: dict[K, tuple[T, Iterator[T]]] | None = None
        for k in mp.keys():
            self._pull(k)

    def __iter__(self) -> Iterator[tuple[K, T]]:
        return self

    def __next__(self) -> tuple[K, T]:
        return self.next()

    def _pull(self, nm: K) -> None:
        try:
            result = next(self._gens[nm])
            heapq.heappush(self._waiting, (result, nm))
        except StopIteration:
            pass
        except IndexError as err:
            raise StopIteration from err

    def next(self) -> tuple[K, T]:
        if self._done is not None:
            raise StopIteration
        try:
            v, nm = heapq.heappop(self._waiting)
            self._pull(nm)
            return (nm, v)
        except IndexError as err:
            raise StopIteration from err

    def stop(self) -> dict[K, tuple[T, Iterator[T]]]:
        """
        Returns the remaining generators, i.e. those that have not
        been pulled. The result is a dictionary with items `(k, (v, vs))`.
        If `v` is not `None`, then it should be pre-pended to `vs`.

        We return things like this in case the value `v` is useful to clients.
        """
        if self._done is None:
            self._done = {nm: (v, self._gens[nm]) for v, nm in self._waiting}
        return self._done


class RolloutInterleaver[K, T]:
    """
    Interleaves multiple generators and provides a `stop` method to
    get the remaining generators back.

    In this setup, the value of type `T` does not need to be comparable
    """

    type Value[U] = tuple[float, U]

    def __init__(self, mp: dict[K, Iterator[RolloutInterleaver.Value[T]]]) -> None:
        self._gens = mp
        self._waiting: list[tuple[float, K, T]] = []
        self._done: (
            dict[K, tuple[tuple[float, T], Iterator[RolloutInterleaver.Value[T]]]]
            | None
        ) = None
        for k in mp.keys():
            self._pull(k)

    def __iter__(self) -> Iterator[tuple[K, RolloutInterleaver.Value[T]]]:
        return self

    def __next__(self) -> tuple[K, RolloutInterleaver.Value[T]]:
        return self.next()

    def _pull(self, nm: K) -> None:
        try:
            pr, result = next(self._gens[nm])
            heapq.heappush(self._waiting, (-pr, nm, result))
        except StopIteration:
            pass
        except IndexError as err:
            raise StopIteration from err

    def next(self) -> tuple[K, RolloutInterleaver.Value[T]]:
        if self._done is not None:
            raise StopIteration
        try:
            pr, nm, value = heapq.heappop(self._waiting)
            self._pull(nm)
            return (nm, (-pr, value))
        except IndexError as err:
            raise StopIteration from err

    def stop(
        self,
    ) -> dict[
        K, tuple[RolloutInterleaver.Value[T], Iterator[RolloutInterleaver.Value[T]]]
    ]:
        """
        Returns the remaining generators, i.e. those that have not
        been pulled. The result is a dictionary with items `(k, (v, vs))`.
        If `v` is not `None`, then it should be pre-pended to `vs`.

        We return things like this in case the value `v` is useful to clients.
        """
        if self._done is None:
            self._done = {
                nm: ((pr, val), self._gens[nm]) for pr, nm, val in self._waiting
            }
        return self._done
