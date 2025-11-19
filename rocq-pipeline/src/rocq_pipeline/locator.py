import logging
import re
from collections.abc import Callable, Sequence
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.schema import task_output

logger = logging.getLogger(__name__)


# BEGIN TODO: define these in terms of (smarter, more efficient) visitors
# for the RocqDocManager.

# TODO: update rocq-doc-manager API to reflect that kind must be
# "command" or "blanks".
def advance_to_first_match(
        rdm: RocqDocManager,
        fn: Callable[[str, str], bool],
        step_over_match: bool = False,
) -> bool:
    """Move rdm to the first matching point. NOTE: proofs are not skipped."""
    prefix = rdm.doc_prefix()
    suffix = rdm.doc_suffix()

    candidate_prefix_matches = [
        (idx, item)
        for idx, item in enumerate(prefix)
        if fn(item.text, item.kind)
    ]
    candidate_suffix_matches = [
        (idx+len(prefix), item)
        for idx, item in enumerate(suffix)
        if fn(item.text, item.kind)
    ]

    def pretty_match_candidates(
            candidates: Sequence[
                tuple[
                    int,
                    RocqDocManager.PrefixItem | RocqDocManager.SuffixItem
                ]
            ],
    ) -> str:
        return "\n".join([
            f"\t- {item.text} of {item.kind} @ idx {idx} \n"
            for idx, item in candidate_prefix_matches
        ])

    # 1a. fast pass: warn if the prefix contains candidate matches; currently,
    # we only advance through the suffix and ignore the prefix
    if candidate_prefix_matches:
        logger.warning("\n".join([
            "Candidate match(es) in the doc prefix are skipped:",
            pretty_match_candidates(candidate_prefix_matches)
        ]))

    # 1b. fast pass: return False if the suffix doesn't contain any matches
    if not candidate_suffix_matches:
        return False

    # 1c. fast pass: warn if the suffix contains multiple candidate matches;
    # currently we only use the first match
    match_idx, match_item = candidate_suffix_matches[0]
    pretty_match = (
        f"{match_item.text} of {match_item.kind} @ idx {match_idx}"
    )
    if len(candidate_suffix_matches) != 1:
        logger.warning("\n".join([
            f"Using first candidate match ({pretty_match}); skipping:",
            pretty_match_candidates(candidate_suffix_matches[1:])
        ]))

    # 2. advance_to the match
    #
    # NOTE: proofs are not skipped
    advance_to_reply = rdm.advance_to(match_idx)
    if isinstance(advance_to_reply, RocqDocManager.Err):
        logger.warning(" ".join([
            f"Failed to advance to the match ({pretty_match}):",
            str(advance_to_reply),
        ]))
        return False

    if step_over_match:
        run_step_reply = rdm.run_step()
        if isinstance(run_step_reply, RocqDocManager.Err):
            logger.warning(
                "Failed to step over the match: {run_step_repl}",
            )
            return False

    return True
# END TODO: define these in terms of (smarter, more efficient) macros


# The interface
class NotFound(Exception):
    pass


class Locator:
    def __call__(self, rdm: RocqDocManager) -> bool:
        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.OtherTask("unknown")
        )


class FirstAdmit(Locator):
    def __str__(self) -> str:
        return 'admit'

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        def is_admit(
                text: str,
                kind: str,
        ) -> bool:
            return kind == "command" and text.startswith("admit")

        return advance_to_first_match(rdm, is_admit)

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.OtherTask("admit")
        )


class FirstLemma(Locator):
    def __str__(self) -> str:
        if self._style is None:
            return f"lemma:{self._name}"
        else:
            return f"{self._style.lower()}:{self._name}"

    def __init__(self, lemma_name: str, style: str | None = None):
        self._name = lemma_name
        self._style = style

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        if self._style is None:
            prefix = "Lemma|Theorem"
        else:
            prefix = self._style

        mtch = re.compile(f"({prefix})\\s+{self._name}[^0-9a-zA-Z_]")

        def is_lemma(
                text: str,
                kind: str,
        ) -> bool:
            return kind == "command" and mtch.match(text) is not None

        if advance_to_first_match(rdm, is_lemma, step_over_match=True):
            for cmd in rdm.doc_suffix():
                if cmd.kind == "blank" or (
                    cmd.kind == "command" and cmd.text.startswith("Proof")
                ):
                    run_step_reply = rdm.run_step()
                    if isinstance(run_step_reply, RocqDocManager.Err):
                        logger.warning(
                            f"RocqDocManager.run_step failed: {run_step_reply}"
                        )
                        return False
                else:
                    return True

        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.FullProofTask()
        )


def parse_locator(s: str) -> Locator:
    if s.startswith("lemma:"):  # Backwards compatibility
        logger.warning(" ".join([
            "\"lemma:\" locator is deprecated,",
            "use \"Theorem:\" or \"Lemma:\":",
            s,
        ]))
        return FirstLemma(s[len("lemma:"):])
    elif s.startswith("Theorem:"):
        return FirstLemma(s[len("Theorem:"):], "Theorem")
    elif s.startswith("Lemma:"):
        return FirstLemma(s[len("Lemma:"):], "Lemma")
    if s == "admit":
        return FirstAdmit()
    return Locator()
