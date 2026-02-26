  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Theorem refl (X : Type) (x : X) : x = x.
  > Proof.
  >   intros X x.
  >   reflexivity.
  > Qed.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > split_sentences [0,"(* xxx *)reflexivity. About nat. (* junk"]
  > split_sentences [0,"(* xxx *)reflexivity. About nat. (* junk *)"]
  > split_sentences [0,"(* xxx *)reflexivity. About nat. (* junk *) more_junk"]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [
          "\nX : Type\nx : X\n============================\nx = x"
        ]
      }
    }
  }
  { "id": 3, "jsonrpc": "2.0", "result": null }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [
          "\nX : Type\nx : X\n============================\nx = x"
        ]
      }
    }
  }
  { "id": 5, "jsonrpc": "2.0", "result": null }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "error": {
      "data": {
        "sentences": [
          { "kind": "blanks", "text": "(* xxx *)" },
          { "kind": "command", "text": "reflexivity." },
          { "kind": "blanks", "text": " " },
          { "kind": "command", "text": "About nat." }
        ],
        "rest": " (* junk"
      },
      "code": -32803,
      "message": "Syntax Error: Lexer: Unterminated comment"
    }
  }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "(* xxx *)" },
      { "kind": "command", "text": "reflexivity." },
      { "kind": "blanks", "text": " " },
      { "kind": "command", "text": "About nat." },
      { "kind": "blanks", "text": " (* junk *)" }
    ]
  }
  {
    "id": 8,
    "jsonrpc": "2.0",
    "error": {
      "data": {
        "sentences": [
          { "kind": "blanks", "text": "(* xxx *)" },
          { "kind": "command", "text": "reflexivity." },
          { "kind": "blanks", "text": " " },
          { "kind": "command", "text": "About nat." }
        ],
        "rest": " (* junk *) more_junk"
      },
      "code": -32803,
      "message": "Syntax error: [ltac_use_default] expected after [tactic] (in [tactic_command])."
    }
  }
