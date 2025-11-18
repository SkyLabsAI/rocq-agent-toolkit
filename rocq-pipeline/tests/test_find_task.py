from pathlib import Path

import pytest

import rocq_pipeline.find_tasks


def test_test_simple() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/test_simple.v"))
    assert len(tasks) == 2
    assert tasks == [{'locator': 'Lemma:is_true','tags': ['proof']},{'locator': 'Lemma:not_false','tags': ['proof']}]


@pytest.mark.skip(reason="temporary: requires pre-building the example")
def test_with_deps() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/with_dep.v"))
    assert len(tasks) == 1
    assert tasks == [{'locator': 'Lemma:add_comm','tags': ['proof']}]

#def test_extract_tactics() -> None:
#    s = "verify_spec; go. wp_for (fun rho => Exists i, i_addr |-> intR 1$m i ** fact_addr |-> longlongR 1$m (fact (Z.to_nat (i - 1))) ** [| (1 <= i <= n+1)%Z |])%I. go.  + assert (fact (Z.to_nat (t - 1)) * t = fact (Z.to_nat t)  )%Z. { specialize (Rfunctions.fact_simpl (Z.to_nat (t - 1))%Z). rewrite <- Z2Nat.inj_succ by(lia). Arith.arith_simpl; lia.  } rewrite H0. specialize (fact_mono(Z.to_nat t)(Z.to_nat n))%Z; intros. go. Arith.arith_simpl; go. + assert (t = n + 1)%Z by(lia). subst t. Arith.arith_simpl; go."
#
#    found, ignored = rocq_pipeline.find_tasks.extract_tactics(s)
#    assert set(found) == {"proof", "Arith.arith_simpl", "rewrite",
#                          "intros", "wp_for", "assert", "go",
#                          "lia", "subst", "verify_spec", "specialize", f"tags ={{{found}}}"}

def test_factorial_longlong() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("../../../psi/data/brick_groundtruth/examples/loopcorpus/Factorial_longlong.v"), tagger=rocq_pipeline.find_tasks.my_tagger)
    assert len(tasks) == 3
    test_ok_inv_task = tasks[2]
    assert test_ok_inv_task['locator'] == 'Lemma:test_ok_inv'
    tags = test_ok_inv_task['tags']
    assert set(tags) == {"proof",
                         "Arith.arith_simpl",
                         "rewrite",
                         "intros",
                         "wp_for",
                         "assert",
                         "go",
                         "lia",
                         "subst",
                         "verify_spec",
                         "specialize"}
