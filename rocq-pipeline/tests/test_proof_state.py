import pytest

# --- Imports from your script ---
# (Assuming your classes are in 'proof_parser.py')
from rocq_pipeline.proof_state import (
    BrickGoal,
    IrisGoal,
    ProofState,
    RocqGoal,
)

# --- Fixture ---
# This fixture provides the parsed proof state to all tests.
# It runs once per module.


@pytest.fixture(scope="module")
def proof_state() -> ProofState:
    """Parses the main example string and returns the ProofState object."""
    pf_state_str: str = (
        '1 goal\n'
        ' \n'
        '  thread_info : biIndex\n'
        '  _Σ : gFunctors\n'
        '  Σ : cpp_logic thread_info _Σ\n'
        '  σ : genv\n'
        '  MOD : source ⊧ σ\n'
        '  _PostPred_ : ptr → mpred\n'
        '  n_addr : ptr\n'
        '  n : Z\n'
        '  PostCond : PostCondition\n'
        '  _H_ : (0 ≤ n)%Z\n'
        '  H : valid<"int"> (n * (n + 1))%Z\n'
        '  sum_addr, i_addr : ptr\n'
        '  GUARDS : GWs.GUARDS\n'
        '  _x_0 : valid<"int"> n\n'
        '  _x_ : valid<"int"> 0%Z\n'
        '  _x_1 : valid<"int"> 1%Z\n'
        '  my_num := 42 : nat\n'
        '  ============================\n'
        '  _ : denoteModule source\n'
        '  _ : type_ptr "int" n_addr\n'
        '  _ : type_ptr "int" sum_addr\n'
        '  _ : type_ptr "int" i_addr\n'
        '  --------------------------------------□\n'
        '  _ : PostCond\n'
        '  _ : n_addr |-> intR 1$m n\n'
        '  _ : sum_addr |-> intR 1$m 0\n'
        '  _ : i_addr |-> intR 1$m 1\n'
        '  --------------------------------------∗\n'
        '  ::wpS\n'
        '    [region: "i" @ i_addr;\n'
        '             "sum" @ sum_addr;\n'
        '             "n" @ n_addr;\n'
        '             return {?: "int"}]\n'
        '    (Sfor None\n'
        '      (Some\n'
        '        (Ebinop Ble (Ecast Cl2r (Evar "i" "int"))\n'
        '          (Ecast Cl2r (Evar "n" "int")) "bool"))\n'
        '      (Some (Epreinc (Evar "i" "int") "int"))\n'
        '      (Sseq\n'
        '        [Sexpr\n'
        '          (Eassign_op Badd (Evar "sum" "int")\n'
        '            (Ecast Cl2r (Evar "i" "int")) "int")]))\n'
        ' \n'
        ' goal 2 (ID 42) is:\n'
        ' \n'
        ' True\n'
        ' \n'
        ' goal 3 (ID 96) is:\n'
        ' --------------------------------------∗\n'
        ' emp')

    # Parse using the most specific type
    return ProofState(pf_state_str, goal_ty_bound=BrickGoal)

# --- Tests ---


def test_proof_state_overview(proof_state: ProofState) -> None:
    """Checks the overall structure of the parsed ProofState."""
    assert len(proof_state.goals) == 3
    assert set(proof_state.goals.keys()) == {1, 2, 3}


def test_goal_1_parsing(proof_state: ProofState) -> None:
    """Checks Goal 1, which should be a full BrickGoal."""
    # Use the typed goal getter, which includes an isinstance check
    goal1 = proof_state.goal(1, strict=True, cast_to=BrickGoal)
    assert goal1 is not None

    # Check metadata
    assert goal1.parts.rocq_rel_goal_num == 1
    # '1 goal' line has no shelved info, so it should be None
    assert goal1.parts.rocq_shelved_cnt is None

    # Check hypothesis parsing
    assert goal1.parts.rocq_hyps["thread_info"] == ("biIndex", None)
    assert goal1.parts.rocq_hyps["sum_addr"] == ("ptr", None)
    assert goal1.parts.rocq_hyps["i_addr"] == ("ptr", None)
    assert goal1.parts.rocq_hyps["my_num"] == ("nat", "42")

    # Check Iris parts
    assert goal1.parts.iris_pers_hyps_anon == {
        'denoteModule source',
        'type_ptr "int" i_addr',
        'type_ptr "int" sum_addr',
        'type_ptr "int" n_addr',
    }
    assert goal1.parts.iris_spat_hyps_anon == {
        'PostCond',
        'i_addr |-> intR 1$m 1',
        'n_addr |-> intR 1$m n',
        'sum_addr |-> intR 1$m 0'
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
