  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.get_env.plugin.
  > Require Import Corelib.Lists.ListDef.
  > Print JSON Environment Corelib.Init.Nat Corelib.Lists.
  > EOF

  $ coqc test.v
  {
    "constants": [
      {
        "kn": "Corelib.Init.Nat.of_hex_int",
        "sn": "Nat.of_hex_int",
        "ty": "(Hexadecimal.signed_int -> option nat)"
      },
      {
        "kn": "Corelib.Init.Nat.of_hex_uint",
        "sn": "Nat.of_hex_uint",
        "ty": "(Hexadecimal.uint -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.to_hex_int",
        "sn": "Nat.to_hex_int",
        "ty": "(nat -> Hexadecimal.signed_int)"
      },
      {
        "kn": "Corelib.Init.Nat.of_uint_acc",
        "sn": "Nat.of_uint_acc",
        "ty": "(Decimal.uint -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.compare",
        "sn": "Nat.compare",
        "ty": "(nat -> nat -> comparison)"
      },
      {
        "kn": "Corelib.Init.Nat.bitwise",
        "sn": "Nat.bitwise",
        "ty": "((bool -> bool -> bool) -> nat -> nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.of_hex_uint_acc",
        "sn": "Nat.of_hex_uint_acc",
        "ty": "(Hexadecimal.uint -> nat -> nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.Forall_sind",
        "sn": "Forall_sind",
        "ty": "(forall (A : Type) (P : A -> Prop) (P0 : list A -> SProp),\n P0 nil ->\n (forall (x : A) (l : list A), P x -> Forall P l -> P0 l -> P0 (x :: l)) ->\n forall l : list A, Forall P l -> P0 l)"
      },
      {
        "kn": "Corelib.Init.Nat.to_hex_uint",
        "sn": "Nat.to_hex_uint",
        "ty": "(nat -> Hexadecimal.uint)"
      },
      {
        "kn": "Corelib.Init.Nat.to_uint",
        "sn": "Nat.to_uint",
        "ty": "(nat -> Decimal.uint)"
      },
      {
        "kn": "Corelib.Init.Nat.testbit",
        "sn": "Nat.testbit",
        "ty": "(nat -> nat -> bool)"
      },
      {
        "kn": "Corelib.Init.Nat.of_num_uint",
        "sn": "Nat.of_num_uint",
        "ty": "(Number.uint -> nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.repeat",
        "sn": "repeat",
        "ty": "(forall A : Type, A -> nat -> list A)"
      },
      {
        "kn": "Corelib.Init.Nat.sqrt_iter",
        "sn": "Nat.sqrt_iter",
        "ty": "(nat -> nat -> nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.log2_iter",
        "sn": "Nat.log2_iter",
        "ty": "(nat -> nat -> nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.firstn",
        "sn": "firstn",
        "ty": "(forall A : Type, nat -> list A -> list A)"
      },
      {
        "kn": "Corelib.Init.Nat.to_int",
        "sn": "Nat.to_int",
        "ty": "(nat -> Decimal.signed_int)"
      },
      {
        "kn": "Corelib.Init.Nat.square",
        "sn": "Nat.square",
        "ty": "(nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.shiftr",
        "sn": "Nat.shiftr",
        "ty": "((fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n)"
      },
      {
        "kn": "Corelib.Init.Nat.shiftl",
        "sn": "Nat.shiftl",
        "ty": "((fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n)"
      },
      {
        "kn": "Corelib.Init.Nat.of_int",
        "sn": "Nat.of_int",
        "ty": "(Decimal.signed_int -> option nat)"
      },
      {
        "kn": "Corelib.Init.Nat.modulo",
        "sn": "Nat.modulo",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.double",
        "sn": "Nat.double",
        "ty": "(nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.divmod",
        "sn": "Nat.divmod",
        "ty": "(nat -> nat -> nat -> nat -> nat * nat)"
      },
      {
        "kn": "Corelib.Init.Nat.tail_addmul",
        "sn": "Nat.tail_addmul",
        "ty": "(nat -> nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.of_uint",
        "sn": "Nat.of_uint",
        "ty": "(Decimal.uint -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.tail_mul",
        "sn": "Nat.tail_mul",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.tail_add",
        "sn": "Nat.tail_add",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.to_num_uint",
        "sn": "Nat.to_num_uint",
        "ty": "(nat -> Number.uint)"
      },
      {
        "kn": "Corelib.Lists.ListDef.skipn",
        "sn": "skipn",
        "ty": "(forall A : Type, nat -> list A -> list A)"
      },
      {
        "kn": "Corelib.Lists.ListDef.seq",
        "sn": "seq",
        "ty": "(nat -> nat -> list nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.nth",
        "sn": "nth",
        "ty": "(forall A : Type, nat -> list A -> A -> A)"
      },
      {
        "kn": "Corelib.Lists.ListDef.map",
        "sn": "map",
        "ty": "(forall A B : Type, (A -> B) -> list A -> list B)"
      },
      {
        "kn": "Corelib.Init.Nat.ldiff",
        "sn": "Nat.ldiff",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.Forall_ind",
        "sn": "Forall_ind",
        "ty": "(forall (A : Type) (P : A -> Prop) (P0 : list A -> Prop),\n P0 nil ->\n (forall (x : A) (l : list A), P x -> Forall P l -> P0 l -> P0 (x :: l)) ->\n forall l : list A, Forall P l -> P0 l)"
      },
      {
        "kn": "Corelib.Init.Nat.to_little_uint",
        "sn": "Nat.to_little_uint",
        "ty": "(nat -> Decimal.uint -> Decimal.uint)"
      },
      { "kn": "Corelib.Init.Nat.zero", "sn": "Nat.zero", "ty": "nat" },
      { "kn": "Corelib.Init.Nat.succ", "sn": "Nat.succ", "ty": "(nat -> nat)" },
      { "kn": "Corelib.Init.Nat.sqrt", "sn": "Nat.sqrt", "ty": "(nat -> nat)" },
      { "kn": "Corelib.Init.Nat.pred", "sn": "Nat.pred", "ty": "(nat -> nat)" },
      {
        "kn": "Corelib.Init.Nat.lxor",
        "sn": "Nat.lxor",
        "ty": "(nat -> nat -> nat)"
      },
      { "kn": "Corelib.Init.Nat.log2", "sn": "Nat.log2", "ty": "(nat -> nat)" },
      {
        "kn": "Corelib.Init.Nat.land",
        "sn": "Nat.land",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.iter",
        "sn": "Nat.iter",
        "ty": "(nat -> forall A : Type, (A -> A) -> A -> A)"
      },
      {
        "kn": "Corelib.Init.Nat.even",
        "sn": "Nat.even",
        "ty": "(nat -> bool)"
      },
      { "kn": "Corelib.Init.Nat.div2", "sn": "Nat.div2", "ty": "(nat -> nat)" },
      { "kn": "Corelib.Init.Nat.two", "sn": "Nat.two", "ty": "nat" },
      {
        "kn": "Corelib.Init.Nat.sub",
        "sn": "Nat.sub",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.pow",
        "sn": "Nat.pow",
        "ty": "(nat -> nat -> nat)"
      },
      { "kn": "Corelib.Init.Nat.one", "sn": "Nat.one", "ty": "nat" },
      { "kn": "Corelib.Init.Nat.odd", "sn": "Nat.odd", "ty": "(nat -> bool)" },
      {
        "kn": "Corelib.Init.Nat.mul",
        "sn": "Nat.mul",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.min",
        "sn": "Nat.min",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.max",
        "sn": "Nat.max",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.ltb",
        "sn": "Nat.ltb",
        "ty": "(nat -> nat -> bool)"
      },
      {
        "kn": "Corelib.Init.Nat.lor",
        "sn": "Nat.lor",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.leb",
        "sn": "Nat.leb",
        "ty": "(nat -> nat -> bool)"
      },
      {
        "kn": "Corelib.Init.Nat.gcd",
        "sn": "Nat.gcd",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.eqb",
        "sn": "Nat.eqb",
        "ty": "(nat -> nat -> bool)"
      },
      {
        "kn": "Corelib.Init.Nat.div",
        "sn": "Nat.div",
        "ty": "(nat -> nat -> nat)"
      },
      {
        "kn": "Corelib.Init.Nat.add",
        "sn": "Nat.add",
        "ty": "(nat -> nat -> nat)"
      },
      { "kn": "Corelib.Init.Nat.t", "sn": "Nat.t", "ty": "Set" },
      {
        "kn": "Corelib.Init.Nat.of_num_int",
        "sn": "Nat.of_num_int",
        "ty": "(Number.signed_int -> option nat)"
      },
      {
        "kn": "Corelib.Lists.ListDef.list_compare",
        "sn": "list_compare",
        "ty": "(forall A : Type, (A -> A -> comparison) -> list A -> list A -> comparison)"
      },
      {
        "kn": "Corelib.Init.Nat.to_num_int",
        "sn": "Nat.to_num_int",
        "ty": "(nat -> Number.signed_int)"
      },
      {
        "kn": "Corelib.Init.Nat.to_num_hex_uint",
        "sn": "Nat.to_num_hex_uint",
        "ty": "(nat -> Number.uint)"
      },
      {
        "kn": "Corelib.Init.Nat.to_little_hex_uint",
        "sn": "Nat.to_little_hex_uint",
        "ty": "(nat -> Hexadecimal.uint -> Hexadecimal.uint)"
      }
    ],
    "inductives": [ { "kn": "Corelib.Lists.ListDef.Forall" } ]
  }
