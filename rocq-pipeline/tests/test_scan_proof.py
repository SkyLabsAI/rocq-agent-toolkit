import itertools

import pytest
from rocq_pipeline.find_tasks import ProofTask, rdm_api, scan_proof


def make_suffix(ls: str, *, ghost: bool = False) -> rdm_api.SuffixItem:
    return rdm_api.SuffixItem(text=ls, kind="ghost" if ghost else "command")


SOME_TACTICS = [["exact I.", "other."], [], ["foo."]]
ALL_BOOL = [True, False]
SOME_WS = [" ", "\t", "\n", "\r\n", "  "]


@pytest.mark.parametrize("tactics, qed", itertools.product(SOME_TACTICS, ALL_BOOL))
def test_simple(tactics: list[str], qed: bool) -> None:
    assert scan_proof(
        [
            make_suffix(s)
            for s in (["Proof."] + tactics + ["Qed." if qed else "Defined."])
        ]
    ) == ProofTask(1, len(tactics) + 1, "qed", tactics)


@pytest.mark.parametrize(
    "tactics, qed",
    itertools.product(SOME_TACTICS, ALL_BOOL),
)
def test_Proof_with(tactics: list[str], qed: bool) -> None:
    assert scan_proof(
        [
            make_suffix(s)
            for s in (["Proof with xxx."] + tactics + ["Qed." if qed else "Defined."])
        ]
    ) == ProofTask(1, len(tactics) + 1, "qed", tactics)


@pytest.mark.parametrize("tactics, qed", itertools.product(SOME_TACTICS, ALL_BOOL))
def test_Proof_using(tactics: list[str], qed: bool) -> None:
    assert scan_proof(
        [
            make_suffix(s)
            for s in (
                ["Proof using\t xxx."] + tactics + ["Qed." if qed else "Defined."]
            )
        ]
    ) == ProofTask(1, len(tactics) + 1, "qed", tactics)


@pytest.mark.parametrize(
    "pre_ws, term, post_ws",
    itertools.product(
        SOME_WS,
        ["hello", "usinghello", "withhello", "(hello bar)"],
        SOME_WS,
    ),
)
def test_Proof_term(pre_ws: str, term: str, post_ws: str):
    assert scan_proof(
        [make_suffix(s) for s in [f"Proof{pre_ws}{term}{post_ws}."]]
    ) == ProofTask(0, 0, "qed", [f"exact {term}."])
