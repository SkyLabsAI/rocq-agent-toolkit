Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
  void test() { }
}}.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "test()" from source as test_spec with
    (\post emp).

  Lemma test_ok : verify[source] "test()".
  Proof.
    verify_spec; go.
  Qed.

End with_cpp.
