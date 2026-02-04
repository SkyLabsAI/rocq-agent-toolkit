import pytest
from rocq_doc_manager import rocq_doc_manager_api as api
from rocq_pipeline.proof_state import (
    IrisGoal,
    ProofState,
    RocqGoal,
)


@pytest.fixture(scope="module")
def focused_goal_strings() -> list[str]:
    return [
        (
            "\n"
            "x : nat\n"
            "y : nat\n"
            "z : nat\n"
            "my_num := 42 : nat\n"
            "============================\n"
            "_ : P x\n"
            "_ : Q y\n"
            "_ : R z\n"
            "_ : S x y\n"
            "--------------------------------------□\n"
            "_ : P a\n"
            "_ : Q b\n"
            "_ : R c\n"
            "_ : T a b\n"
            "--------------------------------------∗\n"
            "P x ∗ Q y ∗ R z"
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
    rdm_pf_state: api.ProofState = api.ProofState(
        focused_goals=focused_goal_strings,
        unfocused_goals=[5, 6],
        shelved_goals=2,
        given_up_goals=1,
    )

    # Parse using the most specific type
    return ProofState(rdm_pf_state, goal_ty_upperbound=IrisGoal)


# --- Tests ---


def test_proof_state_RocqGoal_raw_str(focused_goal_strings, proof_state) -> None:
    for i, focused_goal_string in enumerate(focused_goal_strings, start=1):
        focused_goal: RocqGoal = proof_state.goal(i, strict=True)
        assert focused_goal.raw_str == focused_goal_string


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
    """Checks Goal 1, which should be a full IrisGoal."""
    # Use the typed goal getter, which includes an isinstance check
    goal1 = proof_state.goal(1, strict=True, cast_to=IrisGoal)
    assert goal1 is not None

    # Check metadata
    assert goal1.parts.rocq_rel_goal_num == 1
    assert goal1.parts.rocq_shelved_cnt == 2

    # Check hypothesis parsing
    assert goal1.parts.rocq_hyps["x"] == ("nat", None)
    assert goal1.parts.rocq_hyps["y"] == ("nat", None)
    assert goal1.parts.rocq_hyps["z"] == ("nat", None)
    assert goal1.parts.rocq_hyps["my_num"] == ("nat", "42")

    # Check generic Iris persistent hypotheses
    assert goal1.parts.iris_pers_hyps == {}  # No named persistent hypotheses
    assert goal1.parts.iris_pers_hyps_anon == {
        "P x",
        "Q y",
        "R z",
        "S x y",
    }

    # Check generic Iris spatial hypotheses
    assert goal1.parts.iris_spat_hyps == {}  # No named spatial hypotheses
    assert goal1.parts.iris_spat_hyps_anon == {
        "P a",
        "Q b",
        "R c",
        "T a b",
    }

    # Check generic Iris spatial conclusion
    assert goal1.parts.iris_spat_concl.strip() == "P x ∗ Q y ∗ R z"

    # Check wellformedness
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
    """Checks Goal 3, which is a simple IrisGoal (from 'goal N is:')."""
    goal3 = proof_state.goal(3, strict=True, cast_to=IrisGoal)
    assert goal3 is not None

    # Check metadata
    assert goal3.parts.rocq_rel_goal_num == 3

    # Check 'is_concl_only' parsing
    assert goal3.parts.rocq_hyps == {}
    assert goal3.parts.rocq_concl.strip().startswith("-----------------")

    # Check generic Iris persistent hypotheses
    assert goal3.parts.iris_pers_hyps == {}
    assert goal3.parts.iris_pers_hyps_anon == set()

    # Check generic Iris spatial hypotheses
    assert goal3.parts.iris_spat_hyps == {}
    assert goal3.parts.iris_spat_hyps_anon == set()

    # Check generic Iris spatial conclusion
    assert goal3.parts.iris_spat_concl == "emp"

    # Check wellformedness
    assert goal3.wellformed() is True
