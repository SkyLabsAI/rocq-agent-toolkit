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
  > insert_command [0,"Definition inserted := nat.",false]
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
  > run_step [0]
  > non-existent [0]
  > commit [0,null,false,true]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": { "synterp_ast": { "kind": "synterp:Require", "attrs": {} } }
  }
  { "id": 3, "jsonrpc": "2.0", "result": null }
  { "id": 4, "jsonrpc": "2.0", "result": null }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.inserted" ] },
      "feedback_messages": [
        { "level": "info", "text": "inserted is defined" }
      ],
      "synterp_ast": {
        "kind": "synpure:Definition",
        "attrs": { "id": "inserted", "kind": "Definition" }
      }
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
      ],
      "synterp_ast": { "kind": "synpure:Print", "attrs": {} }
    }
  }
  { "id": 8, "jsonrpc": "2.0", "result": null }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.junk" ] },
      "feedback_messages": [ { "level": "info", "text": "junk is defined" } ],
      "synterp_ast": {
        "kind": "synpure:Definition",
        "attrs": { "id": "junk", "kind": "Definition" }
      }
    }
  }
  { "id": 10, "jsonrpc": "2.0", "result": null }
  {
    "id": 11,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        { "level": "notice", "text": "12 < 42 <= 100\n     : Prop" }
      ],
      "synterp_ast": { "kind": "synpure:CheckMayEval", "attrs": {} }
    }
  }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "offset": 0,
        "text": "Require Import Stdlib.ZArith.BinInt.",
        "data": { "kind": "synterp:Require", "attrs": {} }
      },
      { "kind": "blanks", "offset": 36, "text": "\n\n" },
      { "kind": "blanks", "offset": 38, "text": "\n(* inserted comment *)\n" },
      {
        "kind": "command",
        "offset": 62,
        "text": "Definition inserted := nat.",
        "data": {
          "kind": "synpure:Definition",
          "attrs": { "id": "inserted", "kind": "Definition" }
        }
      },
      { "kind": "blanks", "offset": 89, "text": "\n" },
      {
        "kind": "command",
        "offset": 90,
        "text": "About nil.",
        "data": { "kind": "synpure:Print", "attrs": {} }
      },
      { "kind": "blanks", "offset": 100, "text": "\n    " },
      {
        "kind": "command",
        "offset": 105,
        "text": "Definition junk :=\n\n\nnat.",
        "data": {
          "kind": "synpure:Definition",
          "attrs": { "id": "junk", "kind": "Definition" }
        }
      },
      { "kind": "blanks", "offset": 130, "text": "\n" },
      {
        "kind": "command",
        "offset": 131,
        "text": "Check 12 < 42 <= 100.",
        "data": { "kind": "synpure:CheckMayEval", "attrs": {} }
      }
    ]
  }
  {
    "id": 13,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "\n\n\n" },
      {
        "kind": "command",
        "text": "Theorem test : forall x : nat, x = x.",
        "data": {
          "kind": "synpure:StartTheoremProof",
          "attrs": { "ids": [ "test" ], "kind": "Theorem" }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Proof.",
        "data": { "kind": "synpure:Proof", "attrs": {} }
      },
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "intro x.",
        "data": { "kind": "synterp:Extend", "attrs": {} }
      },
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "reflexivity.",
        "data": { "kind": "synterp:Extend", "attrs": {} }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Qed.",
        "data": { "kind": "synpure:EndProof", "attrs": { "kind": "Qed" } }
      },
      { "kind": "blanks", "text": "\n" }
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
      },
      "synterp_ast": {
        "kind": "synpure:StartTheoremProof",
        "attrs": { "ids": [ "test" ], "kind": "Theorem" }
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
      },
      "synterp_ast": { "kind": "synpure:Proof", "attrs": {} }
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
      },
      "synterp_ast": { "kind": "synterp:Extend", "attrs": {} }
    }
  }
  { "id": 20, "jsonrpc": "2.0", "result": null }
  {
    "id": 21,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": { "given_up_goals": 0, "shelved_goals": 0 },
      "synterp_ast": { "kind": "synterp:Extend", "attrs": {} }
    }
  }
  { "id": 22, "jsonrpc": "2.0", "result": null }
  {
    "id": 23,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.test" ] },
      "synterp_ast": { "kind": "synpure:EndProof", "attrs": { "kind": "Qed" } }
    }
  }
  { "id": 24, "jsonrpc": "2.0", "result": null }
  {
    "id": 25,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method run_step: no step left to run."
    }
  }
  {
    "id": 26,
    "jsonrpc": "2.0",
    "error": { "code": -32601, "message": "Method non-existent not found." }
  }
  { "id": 27, "jsonrpc": "2.0", "result": null }

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
