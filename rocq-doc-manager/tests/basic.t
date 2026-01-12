  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import Stdlib.ZArith.BinInt.
  > 
  > About nil.
  >     Definition junk :=
  > 
  > 
  > nat.
  > Check 12 < 42 <= 100.
  > 
  > 
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > run_step [0]
  > run_step [0]
  > insert_blanks [0,"\n(* inserted comment *)\n"]
  > insert_command [0,"Definition inserted := nat."]
  > insert_blanks [0,"\n"]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > doc_prefix [0]
  > doc_suffix [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > non-existent [0]
  > commit [0,null,true]
  > compile [0]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  { "id": 2, "jsonrpc": "2.0", "result": {} }
  { "id": 3, "jsonrpc": "2.0", "result": null }
  { "id": 4, "jsonrpc": "2.0", "result": null }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.inserted" ] },
      "feedback_messages": [
        { "level": "info", "text": "inserted is defined" }
      ]
    }
  }
  { "id": 6, "jsonrpc": "2.0", "result": null }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        {
          "level": "notice",
          "text": "nil : forall {A : Type}, list A\n\nnil is template universe polymorphic\nArguments nil {A}%_type_scope\nExpands to: Constructor Corelib.Init.Datatypes.nil\nDeclared in library Corelib.Init.Datatypes, line 319, characters 3-6"
        }
      ]
    }
  }
  { "id": 8, "jsonrpc": "2.0", "result": null }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.junk" ] },
      "feedback_messages": [ { "level": "info", "text": "junk is defined" } ]
    }
  }
  { "id": 10, "jsonrpc": "2.0", "result": null }
  {
    "id": 11,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        { "level": "notice", "text": "12 < 42 <= 100\n     : Prop" }
      ]
    }
  }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "offset": 0,
        "text": "Require Import Stdlib.ZArith.BinInt."
      },
      { "kind": "blanks", "offset": 36, "text": "\n\n" },
      { "kind": "blanks", "offset": 38, "text": "\n(* inserted comment *)\n" },
      {
        "kind": "command",
        "offset": 62,
        "text": "Definition inserted := nat."
      },
      { "kind": "blanks", "offset": 89, "text": "\n" },
      { "kind": "command", "offset": 90, "text": "About nil." },
      { "kind": "blanks", "offset": 100, "text": "\n    " },
      {
        "kind": "command",
        "offset": 105,
        "text": "Definition junk :=\n\n\nnat."
      },
      { "kind": "blanks", "offset": 130, "text": "\n" },
      { "kind": "command", "offset": 131, "text": "Check 12 < 42 <= 100." }
    ]
  }
  {
    "id": 13,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "\n\n\n" },
      { "kind": "command", "text": "Theorem test : forall x : nat, x = x." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Proof." },
      { "kind": "blanks", "text": "\n  " },
      { "kind": "command", "text": "intro x." },
      { "kind": "blanks", "text": "\n  " },
      { "kind": "command", "text": "reflexivity." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Qed." }
    ]
  }
  { "id": 14, "jsonrpc": "2.0", "result": null }
  {
    "id": 15,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [
          "\n============================\nforall x : nat, x = x"
        ]
      }
    }
  }
  { "id": 16, "jsonrpc": "2.0", "result": null }
  {
    "id": 17,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [
          "\n============================\nforall x : nat, x = x"
        ]
      }
    }
  }
  { "id": 18, "jsonrpc": "2.0", "result": null }
  {
    "id": 19,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [ "\nx : nat\n============================\nx = x" ]
      }
    }
  }
  { "id": 20, "jsonrpc": "2.0", "result": null }
  {
    "id": 21,
    "jsonrpc": "2.0",
    "result": { "proof_state": { "given_up_goals": 0, "shelved_goals": 0 } }
  }
  { "id": 22, "jsonrpc": "2.0", "result": null }
  {
    "id": 23,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.test" ] }
    }
  }
  {
    "id": 24,
    "jsonrpc": "2.0",
    "error": { "data": null, "code": -32803, "message": "no step left to run" }
  }
  {
    "id": 25,
    "jsonrpc": "2.0",
    "error": { "code": -32601, "message": "Method non-existent not found." }
  }
  { "id": 26, "jsonrpc": "2.0", "result": null }
  {
    "id": 27,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "stdout": "nil : forall {A : Type}, list A\n\nnil is template universe polymorphic\nArguments nil {A}%_type_scope\nExpands to: Constructor Corelib.Init.Datatypes.nil\nDeclared in library Corelib.Init.Datatypes, line 319, characters 3-6\n12 < 42 <= 100\n     : Prop\n",
      "stderr": ""
    }
  }

  $ cat test.v
  Require Import Stdlib.ZArith.BinInt.
  
  
  (* inserted comment *)
  Definition inserted := nat.
  About nil.
      Definition junk :=
  
  
  nat.
  Check 12 < 42 <= 100.
  
  
  Theorem test : forall x : nat, x = x.
  Proof.
    intro x.
    reflexivity.
  Qed.
