(** BEGIN: SKYLABS DEFAULT PROOF IMPORTS *)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.cpp.array.
Import expr_join.
#[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
#[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.
(** END: SKYLABS DEFAULT PROOF IMPORTS *)

Import normalize.only_provable_norm.

(** SCOPES: [bluerock.lang.cpp.parser.plugin.cpp2v] opens a scope that interferes
    with IPM tactic notations.
 *)
Require bluerock.lang.cpp.parser.plugin.cpp2v.

Section code.

cpp.prog source prog cpp:{{
long long test(int n) {
    //Calculates the factorial of n
    long long fact = 1;
    for (int i = 1; i <= n; i++) {
        fact *= i;
    }
    return fact;
}
}}.
End code.

Lemma fact_mono: forall m n : nat,
      (m <= n)%nat ->
      (fact m <= fact n)%Z.
Proof. induction m; intros; simpl.
  + specialize (lt_O_fact n); intros; lia.
  + destruct n. lia.
    assert (m <= n)%nat by lia.
    specialize (IHm n H0). simpl.
    apply inj_le.
    apply Nat.add_le_mono; [ lia |
        apply Nat.mul_le_mono; [ trivial | lia]].
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "test(int)" from source as test_spec with
    (\with n
      \arg "n" (Vint n)
      \require (0 < n)%Z
      \require (valid<"int"> (n+1)%Z)
      \require (valid<"long long"> (Z.of_nat (fact (Z.to_nat n))))
      \post[Vint (Z.of_nat (fact (Z.to_nat n)))] emp).

  Lemma test_ok_inv : verify[source] "test(int)".
  Proof using MOD.
    verify_spec; go.
    wp_for (fun rho => Exists i,
        i_addr |-> intR 1$m i **
        fact_addr |-> longlongR 1$m (fact (Z.to_nat (i - 1))) **
        [| (1 <= i <= n+1)%Z |])%I.
    go.
    + assert (fact (Z.to_nat (t - 1)) * t =
              fact (Z.to_nat t)  )%Z.
      { specialize (Rfunctions.fact_simpl (Z.to_nat (t - 1))%Z).
        rewrite <- Z2Nat.inj_succ by(lia).
        Arith.arith_simpl; lia.  }
      rewrite H0.
      specialize (fact_mono(Z.to_nat t)(Z.to_nat n))%Z; intros.
      go. Arith.arith_simpl; go.
    + Arith.arith_simpl; go.
  Qed.
End with_cpp.
