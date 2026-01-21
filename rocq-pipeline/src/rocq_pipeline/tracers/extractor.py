from collections.abc import Callable, Generator
from pathlib import Path
from typing import Any, override

from rocq_doc_manager import RocqCursor
from rocq_pipeline.proof_state import ProofState


class DocumentWatcher:
    """
    Provides callback infrastructure to watch certain parts of the document.

    When used in a tracing context, it is important that any manipulations of
    the document do not affect the behavior of other parts of the file.
    """

    def extra_paths(self) -> dict[str, Path]:
        return {}

    def setup(self, rdm: RocqCursor) -> None:
        """
        Sets up the infrastructure necessary to run the extractor.

        This is called once **per-file** and should NOT have any user-visible
        side effects in the Rocq document, e.g. it should not alter parsing
        scopes or bring new symbols into scope.
        """
        _ = rdm

    def start_proof(self, rdm: RocqCursor) -> None:
        """
        Function called at the start of a proof.

        This is called once at the start of any proof that is being traced.
        """
        _ = rdm

    def end_proof(self, rdm: RocqCursor) -> None:
        """
        Function called at the end of the proof.

        Note: This occurs after the last tactic invocation. There may
        still be open subgoals if the proof is being closed by `Admitted`.
        """
        _ = rdm


class StateExtractor[T](DocumentWatcher):
    """
    A StateExtractor extracts state from a Rocq proof.
    """

    def __call__(self, rdm: RocqCursor) -> T | None:
        """
        Extract a feature from the current state.
        """
        return None


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


class AllStateExtractor(StateExtractor[dict[str, Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """

    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors: dict[str, StateExtractor[Any]] = extractors

    @override
    def extra_paths(self) -> dict[str, Path]:
        return merge_all(
            (x.extra_paths() for x in self._extractors.values()), super().extra_paths()
        )

    def setup(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.end_proof(rdm)

    @override
    def __call__(self, rdm: RocqCursor) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for k, extract in self._extractors.items():
            # TODO: for now, we assume that extractors are hygeinic in the sense that they do revert any effects they might have on the document.
            # In the future, we could use the revert environment to enforce this.
            try:
                k_result = extract(rdm)
                if k_result is not None:
                    result[k] = k_result
            except Exception:
                pass
        return result


class GoalAsString(StateExtractor[str]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""

    def __call__(self, rdm: RocqCursor) -> str:
        result = rdm.current_goal()
        if isinstance(result, rdm.Err):
            raise RuntimeError("Failed to parse goal: {result}")
        return str(ProofState(result))


class TacticExtractor[B,A](DocumentWatcher):
    """
    Extract information about the execution of a tactic. This class can extract
    additional information based on the tactic, e.g. adding the types of lemmas that
    are used.

    Note that [before] will always be called before [after], so you can pass state
    from the before to the after using the class state.
    """

    def before(self, rdm: RocqCursor, tactic: str) -> B | None:
        return None

    def after(self, rdm: RocqCursor, tactic: str) -> A | None:
        return None


class AllTacticExtractor(TacticExtractor[dict[str, Any],dict[str, Any]]):
    def __init__(self, extractors: dict[str, TacticExtractor[Any,Any]]) -> None:
        self._extractors = extractors

    @override
    def extra_paths(self) -> dict[str, Path]:
        return merge_all(
            (x.extra_paths() for x in self._extractors.values()), super().extra_paths()
        )

    def setup(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        for _, e in self._extractors.items():
            e.end_proof(rdm)

    def before(self, rdm: RocqCursor, tactic: str) -> dict[str, Any] | None:
        def go[B,A](e: TacticExtractor[B,A]) -> B | None:
            try:
                return e.before(rdm, tactic)
            except Exception:
                return None

        return {key: go(e) for key, e in self._extractors.items()}

    def after(self, rdm: RocqCursor, tactic: str) -> dict[str, Any] | None:
        def go[B,A](e: TacticExtractor[B,A]) -> A | None:
            try:
                return e.after(rdm, tactic)
            except Exception:
                return None

        return {key: go(e) for key, e in self._extractors.items()}


class Before[B,A](TacticExtractor[B,A]):
    """Run the StateExtractor before the tactic runs"""

    def __init__(self, state: StateExtractor[B]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqCursor) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        self._extractor.end_proof(rdm)

    @override
    def before(self, rdm: RocqCursor, tactic: str) -> B | None:
        return self._extractor(rdm)


class After[B,A](TacticExtractor[B,A]):
    """Run the StateExtractor after the tactic runs"""

    def __init__(self, state: StateExtractor[A]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqCursor) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        self._extractor.end_proof(rdm)

    @override
    def after(self, rdm: RocqCursor, tactic: str) -> A | None:
        return self._extractor(rdm)


class BeforeAndAfter[T](TacticExtractor[T,T]):
    """Run the StateExtractor before and after the tactic runs"""

    def __init__(self, state: StateExtractor[T]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqCursor) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqCursor) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqCursor) -> None:
        self._extractor.end_proof(rdm)

    @override
    def before(self, rdm: RocqCursor, tactic: str) -> T | None:
        return self._extractor(rdm)

    @override
    def after(self, rdm: RocqCursor, tactic: str) -> T | None:
        return self._extractor(rdm)


class TacticExtractorBuilder:
    @staticmethod
    def of_tactic_extractor[B,A](
        build: Callable[[], TacticExtractor[B,A]] | type[TacticExtractor[B,A]],
    ) -> "TacticExtractorBuilder":
        return TacticExtractorBuilder(build)

    def __init__(self, build: Callable[[], TacticExtractor[Any,Any]]) -> None:
        self._builder = build

    def build(self) -> TacticExtractor[Any,Any]:
        return self._builder()
