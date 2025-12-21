import re

import pytest
from rocq_doc_manager import RocqDocManager as RDM
from rocq_pipeline.proof_state import (
    BrickGoal,
    IrisGoal,
    ProofState,
    RocqGoal,
)


@pytest.fixture(scope="module")
def focused_goal_strings() -> list[str]:
    return [
        (
            "\n"
            "thread_info : biIndex\n"
            "_Σ : gFunctors\n"
            "Σ : cpp_logic thread_info _Σ\n"
            "σ : genv\n"
            "MOD : source ⊧ σ\n"
            "_PostPred_ : ptr → mpred\n"
            "n_addr : ptr\n"
            "n : Z\n"
            "PostCond : PostCondition\n"
            "_H_ : (0 ≤ n)%Z\n"
            'H : valid<"int"> (n * (n + 1))%Z\n'
            "sum_addr, i_addr : ptr\n"
            "GUARDS : GWs.GUARDS\n"
            '_x_0 : valid<"int"> n\n'
            '_x_ : valid<"int"> 0%Z\n'
            '_x_1 : valid<"int"> 1%Z\n'
            "my_num := 42 : nat\n"
            "============================\n"
            "_ : denoteModule source\n"
            '_ : type_ptr "int" n_addr\n'
            '_ : type_ptr "int" sum_addr\n'
            '_ : type_ptr "int" i_addr\n'
            "--------------------------------------□\n"
            "_ : PostCond\n"
            "_ : n_addr |-> intR 1$m n\n"
            "_ : sum_addr |-> intR 1$m 0\n"
            "_ : i_addr |-> intR 1$m 1\n"
            "--------------------------------------∗\n"
            "::wpS\n"
            '  [region: "i" @ i_addr;\n'
            '           "sum" @ sum_addr;\n'
            '           "n" @ n_addr;\n'
            '           return {?: "int"}]\n'
            "  (Sfor None\n"
            "    (Some\n"
            '      (Ebinop Ble (Ecast Cl2r (Evar "i" "int"))\n'
            '        (Ecast Cl2r (Evar "n" "int")) "bool"))\n'
            '    (Some (Epreinc (Evar "i" "int") "int"))\n'
            "    (Sseq\n"
            "      [Sexpr\n"
            '        (Eassign_op Badd (Evar "sum" "int")\n'
            '          (Ecast Cl2r (Evar "i" "int")) "int")]))\n'
        ),
        ("\n============================\n True\n"),
        (
            "\n"
            "============================\n"
            "--------------------------------------∗\n"
            "emp"
        ),
        (
            "\n"
            " ============================\n"
            "emp\n"
            "--------------------------------------□\n"
            "--------------------------------------∗\n"
            "emp"
        ),
    ]


@pytest.fixture(scope="module")
def proof_state(focused_goal_strings) -> ProofState:
    """Parses the main example string and returns the ProofState object."""
    rdm_pf_state: RDM.ProofState = RDM.ProofState(
        focused_goals=focused_goal_strings,
        unfocused_goals=[5, 6],
        shelved_goals=2,
        given_up_goals=1,
    )

    # Parse using the most specific type
    return ProofState(rdm_pf_state, goal_ty_upperbound=BrickGoal)


# --- Tests ---


def test_proof_state_RocqGoal_raw_str(focused_goal_strings, proof_state) -> None:
    for i, focused_goal_string in enumerate(focused_goal_strings, start=1):
        focused_goal: RocqGoal = proof_state.goal(i, strict=True)
        assert focused_goal.raw_str == focused_goal_string


def test_BrickGoal_is_loop_goal1(proof_state) -> None:
    goal = proof_state.goal(1, strict=True, cast_to=BrickGoal)
    assert (
        bool(goal.regex_brick_spat_concl_wp("Sdo_while", "Sfor", "Swhile", kind="S"))
        is True
    )


def test_BrickGoal_is_loop_goal3(proof_state) -> None:
    goal = proof_state.goal(3, strict=True, cast_to=BrickGoal)

    d: dict[str, re.Match[str] | None] = goal.regex_brick_spat_concl_wp(
        "Sfor", "Swhile", "Sdo_while"
    )
    b: bool = any(value is not None for value in d.values())
    assert b is False


def test_proof_state_None() -> None:
    pf_state = ProofState(None)
    assert pf_state.closed()


def test_proof_state_overview(proof_state: ProofState) -> None:
    """Checks the overall structure of the parsed ProofState."""
    assert proof_state.unfocused_goals == [5, 6]
    assert len(proof_state.goals) == 4
    assert set(proof_state.goals.keys()) == {1, 2, 3, 4}

    for idx, g in proof_state.goals.items():
        assert g.parts.rocq_rel_goal_num == idx
        assert g.parts.rocq_shelved_cnt == proof_state.shelved_cnt
        assert g.parts.rocq_admit_cnt == proof_state.admit_cnt


def test_goal_1_parsing(proof_state: ProofState) -> None:
    """Checks Goal 1, which should be a full BrickGoal."""
    # Use the typed goal getter, which includes an isinstance check
    goal1 = proof_state.goal(1, strict=True, cast_to=BrickGoal)
    assert goal1 is not None

    # Check metadata
    assert goal1.parts.rocq_rel_goal_num == 1
    assert goal1.parts.rocq_shelved_cnt == 2

    # Check hypothesis parsing
    assert goal1.parts.rocq_hyps["thread_info"] == ("biIndex", None)
    assert goal1.parts.rocq_hyps["sum_addr"] == ("ptr", None)
    assert goal1.parts.rocq_hyps["i_addr"] == ("ptr", None)
    assert goal1.parts.rocq_hyps["my_num"] == ("nat", "42")

    # Check Iris parts
    assert goal1.parts.iris_pers_hyps_anon == {
        "denoteModule source",
        'type_ptr "int" i_addr',
        'type_ptr "int" sum_addr',
        'type_ptr "int" n_addr',
    }
    assert goal1.parts.iris_spat_hyps_anon == {
        "PostCond",
        "i_addr |-> intR 1$m 1",
        "n_addr |-> intR 1$m n",
        "sum_addr |-> intR 1$m 0",
    }
    assert goal1.parts.iris_spat_concl.strip().startswith("::wpS")

    # Check Brick-specific behavior
    assert goal1.is_loop_goal() is True
    assert goal1.wellformed() is True


def test_goal_2_parsing(proof_state: ProofState) -> None:
    """Checks Goal 2, which should fall back to a base RocqGoal."""
    # 1. Get the goal
    goal2 = proof_state.goal(2, strict=True)
    assert goal2 is not None

    # 2. Check type (THE MOST IMPORTANT CHECK)
    # It must be a RocqGoal, but *not* a more specific IrisGoal
    assert isinstance(goal2, RocqGoal)
    assert not isinstance(goal2, IrisGoal)

    # 3. Check properties
    assert goal2.parts.rocq_rel_goal_num == 2
    assert goal2.parts.rocq_concl == "True"
    assert goal2.wellformed() is True

    # 4. Check that a strict cast to a wrong type fails
    with pytest.raises(TypeError, match="not the requested type IrisGoal"):
        proof_state.goal(2, strict=True, cast_to=IrisGoal)

    # 5. Check that a non-strict cast to a wrong type returns None
    assert proof_state.goal(2, strict=False, cast_to=IrisGoal) is None


def test_goal_3_parsing(proof_state: ProofState) -> None:
    """Checks Goal 3, which is a simple BrickGoal (from 'goal N is:')."""
    goal3 = proof_state.goal(3, strict=True, cast_to=BrickGoal)
    assert goal3 is not None

    # Check metadata
    assert goal3.parts.rocq_rel_goal_num == 3

    # Check 'is_concl_only' parsing
    assert goal3.parts.rocq_hyps == {}
    assert goal3.parts.rocq_concl.strip().startswith("-----------------")
    assert goal3.parts.iris_spat_concl == "emp"

    # Check behavior
    assert goal3.is_loop_goal() is False
    assert goal3.wellformed() is True
