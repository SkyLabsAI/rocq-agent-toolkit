from collections.abc import Callable, Generator
from pathlib import Path
from typing import Any, Protocol

from rocq_doc_manager import RocqCursor


class NotSupported(Exception):
    """
    Is used to signal that an extractor does not support tracing a certain
    command or tactic.
    """

    pass


class DocumentWatcher(Protocol):
    """
    Provides callback infrastructure to watch certain parts of the document.

    When used in a tracing context, it is important that any manipulations of
    the document do not affect the behavior of other parts of the file.
    """

    def extra_paths(self) -> dict[str, Path]: ...

    def setup(self, rdm: RocqCursor) -> None:
        """
        Sets up the infrastructure necessary to run the extractor.

        This is called once **per-file** and should NOT have any user-visible
        side effects in the Rocq document, e.g. it should not alter parsing
        scopes or bring new symbols into scope.
        """
        ...

    def start_proof(self, rdm: RocqCursor) -> None:
        """
        Function called at the start of a proof.

        This is called once at the start of any proof that is being traced.
        """
        ...

    def end_proof(self, rdm: RocqCursor) -> None:
        """
        Function called at the end of the proof.

        Note: This occurs after the last tactic invocation. There may
        still be open subgoals if the proof is being closed by `Admitted`.
        """
        ...


class DefaultDocumentWatcher(DocumentWatcher):
    def extra_paths(self) -> dict[str, Path]:
        return {}

    def setup(self, rdm: RocqCursor) -> None:
        pass

    def start_proof(self, rdm: RocqCursor) -> None:
        pass

    def end_proof(self, rdm: RocqCursor) -> None:
        pass


class StateExtractor[T](Protocol):
    """
    A StateExtractor extracts state from a Rocq proof.
    """

    def extract(self, rdm: RocqCursor) -> T:
        """
        Extract a feature from the current state.
        """
        ...


def merge_into[A, B](a: dict[A, B], b: dict[A, B]) -> None:
    for k, v in b.items():
        if k in a and a[k] != v:
            raise ValueError("Overlapping entries")
        a[k] = v


def merge_all[A, B](
    ds: Generator[dict[A, B]], into: dict[A, B] | None = None
) -> dict[A, B]:
    result: dict[A, B] = {} if into is None else into
    for x in ds:
        merge_into(result, x)
    return result


class AllDocumentWatcher(DocumentWatcher):
    """
    Produce an object that contains the results of all of the state extractors
    """

    def __init__(self, watchers: dict[str, DocumentWatcher]):
        self._watchers: dict[str, DocumentWatcher] = watchers

    def extra_paths(self) -> dict[str, Path]:
        return merge_all(w.extra_paths() for w in self._watchers.values())

    def setup(self, rdm: RocqCursor) -> None:
        for _, w in self._watchers.items():
            w.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        for _, w in self._watchers.items():
            w.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        for _, w in self._watchers.items():
            w.end_proof(rdm)


class AllStateExtractor(StateExtractor[dict[str, Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """

    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors: dict[str, StateExtractor[Any]] = extractors

    def extract(self, rdm: RocqCursor) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for k, extractor in self._extractors.items():
            # TODO: for now, we assume that extractors are hygeinic in the sense that they do revert any effects they might have on the document.
            # In the future, we could use the revert environment to enforce this.
            try:
                k_result = extractor.extract(rdm)
                if k_result is not None:
                    result[k] = k_result
            except NotSupported:
                pass
        return result


type After[A] = Callable[[RocqCursor, str], A]


class BracketInterface[A](Protocol):
    """
    Is used internally to enforce the [before]-before-[after] invariant of
    [BracketedExtractor].

    Inheriting from [BracketedExtractor] automatically implements this interface.
    """

    def before_internal(self, rdm: RocqCursor, tactic: str) -> After[A]: ...


class BracketedExtractor[B, A](BracketInterface[A], Protocol):
    """
    Extract information about the execution of a command (or a tactic). Classes
    implementing this protocol can extract additional information based on the
    command, e.g. adding the types of lemmas that are used in a tactic.

    Note that [before] will always be called before [after] and the return value
    of [before] is passed to [after] as the [result_before] value.
    """

    def before(self, rdm: RocqCursor, tactic: str) -> B: ...

    def after(self, rdm: RocqCursor, tactic: str, result_before: B) -> A: ...

    def before_internal(self, rdm: RocqCursor, tactic: str) -> After[A]:
        result_before = self.before(rdm, tactic)
        return lambda rdm, tactic: self.after(rdm, tactic, result_before)


class TrivialBracketedExtractor[A](StateExtractor[A], BracketedExtractor[A, A]):
    def before(self, rdm: RocqCursor, tactic: str) -> A:
        return self.extract(rdm)

    def after(self, rdm: RocqCursor, tactic: str, result_before: A) -> A:
        return self.extract(rdm)


type D = dict[str, Any]


class AllBracketedExtractor(BracketedExtractor[D, D]):
    def __init__(self, extractors: dict[str, BracketedExtractor[Any, Any]]) -> None:
        self._extractors = extractors

    def before(self, rdm: RocqCursor, tactic: str) -> D:
        state = {}
        for k, e in self._extractors.items():
            try:
                state[k] = e.before(rdm, tactic)
            except NotSupported:
                pass
        return state

    def after(self, rdm: RocqCursor, tactic: str, result_before) -> D:
        results: D = {}
        for k, e in result_before.items():
            try:
                results[k] = self._extractors[k].after(rdm, tactic, result_before=e)
            except NotSupported:
                pass
        return results


class Tracer[A](DocumentWatcher, BracketInterface[A], Protocol):
    """
    The protocol that the tracer relies on.
    """

    pass
