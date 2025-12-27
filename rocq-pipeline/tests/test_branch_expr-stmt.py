import pytest
from rocq_doc_manager import RocqDocManager as RDM
from rocq_pipeline.proof_state import (
    BrickGoal,
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
            "s_addr : ptr\n"
            "GUARDS : GUARDS\n"
            '_x_0 : valid<"int"> n\n'
            "============================\n"
            "_ : denoteModule source\n"
            '_ : type_ptr "int" n_addr\n'
            '_ : type_ptr "int" s_addr\n'
            "--------------------------------------□\n"
            "_ : PostCond\n"
            '_ : s_addr |-> uninitR "int" 1$m\n'
            "_ : n_addr |-> intR 1$m n\n"
            "--------------------------------------∗\n"
            "branch.stmt source\n"
            '  [region: "s" @ s_addr;\n'
            '            "n" @ n_addr;\n'
            '            return {?: "int"}]\n'
            "(bool_decide (n > 0))\n"
            '(Sseq [Sexpr (Eassign (Evar "s" "int") (Eint 1 "int") "int")])\n'
            '(Sif None (Ebinop Blt (Ecast Cl2r (Evar "n" "int")) (Eint 0 "int") "bool")\n'
            '(Sseq [Sexpr (Eassign (Evar "s" "int") (Eunop Uminus (Eint 1 "int") "int") "int")])\n'
            '(Sseq [Sexpr (Eassign (Evar "s" "int") (Eint 0 "int") "int")]))\n'
            "(Kseq\n"
            '   (wp_block source [region: "s" @ s_addr; "n" @ n_addr; return {?: "int"}]\n'
            '     [Sreturn (Some (Ecast Cl2r (Evar "s" "int")))])\n'
            '   (Kfree source (1 >*> FreeTemps.delete "int" s_addr)\n'
            "      (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v)))))\n"
        ),
        (
            "\n"
            "thread_info : biIndex\n"
            "_Σ : gFunctors\n"
            "Σ : cpp_logic thread_info _Σ\n"
            "σ : genv\n"
            "MOD : source ⊧ σ\n"
            "_PostPred_ : ptr → mpred\n"
            "x_addr : ptr\n"
            "x : bool\n"
            "PostCond : PostCondition\n"
            "GUARDS : GUARDS\n"
            '_x_0 : valid<"bool"> (Vbool x)\n'
            "i_addr : ptr\n"
            "============================\n"
            "_ : denoteModule source\n"
            '_ : type_ptr "bool" x_addr\n'
            "--------------------------------------□\n"
            "_ : PostCond\n"
            "_ : x_addr |-> boolR 1$m x\n"
            "--------------------------------------∗\n"
            "branch.expr source\n"
            '   [region: "i" @ i_addr; "x" @ x_addr; return {?: "int"}] x (Eint 0 "int") (Eint 1 "int")\n'
            "(λ (v : val) (free' : FreeTemps),\n"
            'i_addr |-> primR "int" 1$m v -∗\n'
            "interp source (free' >*> 1)\n"
            '(wp_decls source [region: "i" @ i_addr; "x" @ x_addr; return {?: "int"}] []\n'
            "(λ (ρ : region) (free'0 : FreeTemps),\n"
            "▷ wp_block source ρ [Sreturn (Some (Ecast Cl2r [...]))]\n"
            "(Kfree source (free'0 >*> FreeTemps.delete \n"
            '"int" i_addr) (Kcleanup source [] ([...]))))))'
        ),
    ]


@pytest.fixture(scope="module")
def proof_state(focused_goal_strings) -> ProofState:
    """Parses the main example string and returns the ProofState object."""
    rdm_pf_state: RDM.ProofState = RDM.ProofState(
        focused_goals=focused_goal_strings,
        unfocused_goals=[],
        shelved_goals=0,
        given_up_goals=0,
    )

    # Parse using the most specific type
    return ProofState(rdm_pf_state, goal_ty_upperbound=BrickGoal)


# --- Tests ---


def test_branch_RocqGoal_raw_str(focused_goal_strings, proof_state) -> None:
    for i, focused_goal_string in enumerate(focused_goal_strings, start=1):
        focused_goal: RocqGoal = proof_state.goal(i, strict=True)
        assert focused_goal.raw_str == focused_goal_string


def test_BrickGoal_is_branch_expr_goal_goal1(proof_state) -> None:
    goal = proof_state.goal(1, strict=True, cast_to=BrickGoal)
    assert bool(goal.is_branch_expr_goal()) is False


def test_BrickGoal_is_branch_stmt_goal_goal1(proof_state) -> None:
    goal = proof_state.goal(1, strict=True, cast_to=BrickGoal)
    assert bool(goal.is_branch_stmt_goal()) is True


def test_BrickGoal_is_branch_expr_goal_goal2(proof_state) -> None:
    goal = proof_state.goal(2, strict=True, cast_to=BrickGoal)
    assert bool(goal.is_branch_expr_goal()) is True


def test_BrickGoal_is_branch_stmt_goal_goal2(proof_state) -> None:
    goal = proof_state.goal(2, strict=True, cast_to=BrickGoal)
    assert bool(goal.is_branch_stmt_goal()) is False
