  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Theorem demo : nat -> True.
  > Proof.
  >   intro n.
  >   set (x := n).
  > Abort.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > structured_goals [0]
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
        "focused_goals": [ "\n============================\nnat -> True" ]
      },
      "synterp_ast": {
        "kind": "StartTheoremProof",
        "pure": true,
        "attrs": { "ids": [ "demo" ], "kind": "Theorem" }
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
        "focused_goals": [ "\n============================\nnat -> True" ]
      },
      "synterp_ast": { "kind": "Proof", "pure": true, "attrs": {} }
    }
  }
  { "id": 5, "jsonrpc": "2.0", "result": null }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [ "\nn : nat\n============================\nTrue" ]
      },
      "synterp_ast": { "kind": "Extend", "attrs": {} }
    }
  }
  { "id": 7, "jsonrpc": "2.0", "result": null }
  {
    "id": 8,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [
          "\nn : nat\nx := n : nat\n============================\nTrue"
        ]
      },
      "synterp_ast": { "kind": "Extend", "attrs": {} }
    }
  }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "result": [
      {
        "hyps": [
          { "name": "n", "type": "nat" },
          { "name": "x", "def": "n", "type": "nat" }
        ],
        "goal": "True"
      }
    ]
  }
