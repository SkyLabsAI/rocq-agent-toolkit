  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Theorem refl (X : Type) (x : X) : x = x.
  > Proof.
  >   intros X x.
  >   reflexivity.
  > Qed.
  > Module ttt.
  > End ttt.
  > Module uuu := ttt.
  > Module Type XXX.
  > End XXX.
  > Module Type YYY := XXX.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > doc_suffix [0]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "text": "Theorem refl (X : Type) (x : X) : x = x.",
        "data": {
          "kind": "StartTheoremProof",
          "pure": true,
          "attrs": { "ids": [ "refl" ], "kind": "Theorem" }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Proof.",
        "data": { "kind": "Proof", "pure": true, "attrs": {} }
      },
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "intros X x.",
        "data": { "kind": "Extend", "attrs": {} }
      },
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "reflexivity.",
        "data": { "kind": "Extend", "attrs": {} }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Qed.",
        "data": {
          "kind": "EndProof",
          "pure": true,
          "attrs": { "kind": "Qed" }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Module ttt.",
        "data": {
          "kind": "DefineModule",
          "attrs": { "id": "ttt", "defn": false }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "End ttt.",
        "data": { "kind": "EndSegment", "attrs": { "id": "ttt" } }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Module uuu := ttt.",
        "data": {
          "kind": "DefineModule",
          "attrs": { "id": "uuu", "defn": true }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Module Type XXX.",
        "data": {
          "kind": "DeclareModuleType",
          "attrs": { "id": "XXX", "defn": false }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "End XXX.",
        "data": { "kind": "EndSegment", "attrs": { "id": "XXX" } }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Module Type YYY := XXX.",
        "data": {
          "kind": "DeclareModuleType",
          "attrs": { "id": "YYY", "defn": true }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ]
  }
