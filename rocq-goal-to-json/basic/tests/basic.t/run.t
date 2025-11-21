  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ dune build
  { "hyps": [], "goal": "True" }
  { "hyps": [], "goal": "(True -> True)" }
  { "hyps": [], "goal": "(let x : True := I in False)" }
  { "hyps": [ { "name": "x", "type": "True", "def": "I" } ], "goal": "False" }
  { "hyps": [], "goal": "(forall a b : Prop, a -> a /\\ b)" }
  {
    "hyps": [ { "name": "a", "type": "Prop" } ],
    "goal": "(forall b : Prop, a -> a /\\ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" }, { "name": "b", "type": "Prop" }
    ],
    "goal": "(a -> a /\\ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "(a /\\ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "b"
  }
  { "hyps": [], "goal": "(forall a b : Prop, a -> a /\\ b)" }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "(a /\\ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "b"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "a"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "H", "type": "a" }
    ],
    "goal": "b"
  }
  File "./test.v", line 56, characters 2-9:
  Warning: The Focus command is deprecated; use '1: {' instead.
  [deprecated-focus,deprecated-since-8.8,deprecated,default]
