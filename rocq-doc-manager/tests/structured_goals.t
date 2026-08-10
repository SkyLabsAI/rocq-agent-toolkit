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
      },
      "loc": {
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 0,
        "ep": 27
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
      "synterp_ast": { "kind": "Proof", "pure": true, "attrs": {} },
      "loc": {
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 28,
        "ep": 34
      }
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
      "synterp_ast": { "kind": "Extend", "attrs": {} },
      "loc": {
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 37,
        "ep": 45
      }
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
      "synterp_ast": { "kind": "Extend", "attrs": {} },
      "loc": {
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 48,
        "ep": 61
      }
    }
  }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "result": [
      {
        "hyps": [
          { "name": "n", "type": "nat" },
          { "name": "x", "defn": "n", "type": "nat" }
        ],
        "goal": "True"
      }
    ]
  }
