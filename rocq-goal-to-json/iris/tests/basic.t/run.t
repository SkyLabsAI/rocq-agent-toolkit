  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ dune build
  { "hyps": [], "goal": "True" }
  { "hyps": [], "goal": "(True → True)" }
  { "hyps": [], "goal": "(let x : True := I in False)" }
  { "hyps": [ { "name": "x", "type": "True", "def": "I" } ], "goal": "False" }
  { "hyps": [], "goal": "(∀ a b : Prop, a → a ∧ b)" }
  {
    "hyps": [ { "name": "a", "type": "Prop" } ],
    "goal": "(∀ b : Prop, a → a ∧ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" }, { "name": "b", "type": "Prop" }
    ],
    "goal": "(a → a ∧ b)"
  }
  {
    "hyps": [
      { "name": "a", "type": "Prop" },
      { "name": "b", "type": "Prop" },
      { "name": "HH", "type": "a" }
    ],
    "goal": "(a ∧ b)"
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "goal": "(P ⊢ P ∗ emp)"
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "(P -∗ P ∗ emp)%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P", "emp%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "emp%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "emp%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "emp%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "emp%I" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [ { "name": "H", "prop": "P" } ],
    "concls": [ "P" ]
  }
  {
    "hyps": [
      { "name": "PROP", "type": "bi" },
      { "name": "P", "type": "(bi_car PROP)" }
    ],
    "pers_hyps": [],
    "spat_hyps": [],
    "concls": [ "emp%I" ]
  }
