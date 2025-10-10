(*|
# Verifying a Simple Function

Our first proof will be about a very simple function:

```cpp
void test() { }
```

This is trivial, but it lets us learn the basics about verification.

## Setting up the Verification

Import the C++ verification environment:
|*)
Require Import bluerock.auto.cpp.prelude.proof.

(*| Import a command to specify our C++ program "inline". |*)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

(*|

Define AST `source` containing the code above: |*)
cpp.prog source prog cpp:{{
  void test() { }
}}.

(*|
Some more setup is omitted for now.
|*)
(*@HIDE@*)
Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

(*@END-HIDE@*)

(*|
## Specifying the Expected Behavior

We must first specify what the `test` function does.
|*)
cpp.spec "test()" from source as test_spec with
  (\post emp).
(*|
This specification states that `test()` does nothing.
The `\post emp` tells you that the function doesn't return any {{ "resource" | terminology }}, but we'll get into that more later.

## Verifying the Function

Now, we can set up the verification by posing a `Lemma`.
|*)
Lemma test_ok : verify[source] "test()".
Proof.
(*|
This sets up a theorem for our function that states that the function satisfies the specification, and that invoking the function
as specified will not produce any {{ "undefined behavior" | terminology }}.

Since this is a particularly simple function, the proof is also simple. This proceeds in two stages:
1. We use `verify_spec` to begin the proof: our goal becomes a goal about the concrete function body.
2. Next we use the `go` tactic to {{ "symbolically execute" | terminology }} the body of the function and prove the post-condition.

Idiomatically, we chain these two tactics together using a `;` which leads us to the following proof script.
|*)
  verify_spec; go.
Qed.
(*|
The `Qed` ends the proof and Rocq tells us that the proof is checked.

Congratulations! You've walked through your first proof.
|*)

(*@HIDE@*)
(*|
## What's Next?

Consider verifying some more simple functions including:

|*)

End with_cpp.
(*@END-HIDE@*)
