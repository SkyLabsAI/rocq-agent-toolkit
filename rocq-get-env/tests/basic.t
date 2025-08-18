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
        "kername": "Corelib.Init.Nat.of_hex_int",
        "about": "Nat.of_hex_int : Hexadecimal.signed_int -> option nat\n\nNat.of_hex_int is not universe polymorphic\nArguments Nat.of_hex_int d%_hex_int_scope\nNat.of_hex_int is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_int\nDeclared in library Corelib.Init.Nat, line 249, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Nat.of_hex_uint",
        "about": "Nat.of_hex_uint : Hexadecimal.uint -> nat\n\nNat.of_hex_uint is not universe polymorphic\nArguments Nat.of_hex_uint d%_hex_uint_scope\nNat.of_hex_uint is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_uint\nDeclared in library Corelib.Init.Nat, line 213, characters 11-22"
      },
      {
        "kername": "Corelib.Init.Nat.to_hex_int",
        "about": "Nat.to_hex_int : nat -> Hexadecimal.signed_int\n\nNat.to_hex_int is not universe polymorphic\nArguments Nat.to_hex_int n%_nat_scope\nNat.to_hex_int is transparent\nExpands to: Constant Corelib.Init.Nat.to_hex_int\nDeclared in library Corelib.Init.Nat, line 263, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Nat.of_uint_acc",
        "about": "Nat.of_uint_acc : Decimal.uint -> nat -> nat\n\nNat.of_uint_acc is not universe polymorphic\nArguments Nat.of_uint_acc d acc%_nat_scope\nNat.of_uint_acc is transparent\nExpands to: Constant Corelib.Init.Nat.of_uint_acc\nDeclared in library Corelib.Init.Nat, line 173, characters 9-20"
      },
      {
        "kername": "Corelib.Init.Nat.compare",
        "about": "Nat.compare : nat -> nat -> comparison\n\nNat.compare is not universe polymorphic\nArguments Nat.compare (n m)%_nat_scope\nNat.compare is transparent\nExpands to: Constant Corelib.Init.Nat.compare\nDeclared in library Corelib.Init.Nat, line 104, characters 9-16"
      },
      {
        "kername": "Corelib.Init.Nat.bitwise",
        "about": "Nat.bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat\n\nNat.bitwise is not universe polymorphic\nArguments Nat.bitwise op%_function_scope (n a b)%_nat_scope\nNat.bitwise is transparent\nExpands to: Constant Corelib.Init.Nat.bitwise\nDeclared in library Corelib.Init.Nat, line 416, characters 9-16"
      },
      {
        "kername": "Corelib.Init.Nat.of_hex_uint_acc",
        "about": "Nat.of_hex_uint_acc : Hexadecimal.uint -> nat -> nat\n\nNat.of_hex_uint_acc is not universe polymorphic\nArguments Nat.of_hex_uint_acc d acc%_nat_scope\nNat.of_hex_uint_acc is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_uint_acc\nDeclared in library Corelib.Init.Nat, line 192, characters 9-24"
      },
      {
        "kername": "Corelib.Lists.ListDef.Forall_sind",
        "about": "Forall_sind :\nforall [A : Type] [P : A -> Prop] (P0 : list A -> SProp),\nP0 nil ->\n(forall (x : A) (l : list A), P x -> Forall P l -> P0 l -> P0 (x :: l)) ->\nforall [l : list A], Forall P l -> P0 l\n\nForall_sind is not universe polymorphic\nArguments Forall_sind [A]%_type_scope [P]%_function_scope \n  P%_function_scope f f0%_function_scope [l]%_list_scope \n  f\nForall_sind is transparent\nExpands to: Constant Corelib.Lists.ListDef.Forall_sind\nDeclared in library Corelib.Lists.ListDef, line 114, characters 4-142"
      },
      {
        "kername": "Corelib.Init.Nat.to_hex_uint",
        "about": "Nat.to_hex_uint : nat -> Hexadecimal.uint\n\nNat.to_hex_uint is not universe polymorphic\nArguments Nat.to_hex_uint n%_nat_scope\nNat.to_hex_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_hex_uint\nDeclared in library Corelib.Init.Nat, line 236, characters 11-22"
      },
      {
        "kername": "Corelib.Init.Nat.to_uint",
        "about": "Nat.to_uint : nat -> Decimal.uint\n\nNat.to_uint is not universe polymorphic\nArguments Nat.to_uint n%_nat_scope\nNat.to_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_uint\nDeclared in library Corelib.Init.Nat, line 227, characters 11-18"
      },
      {
        "kername": "Corelib.Init.Nat.testbit",
        "about": "Nat.testbit : nat -> nat -> bool\n\nNat.testbit is not universe polymorphic\nArguments Nat.testbit (a n)%_nat_scope\nNat.testbit is transparent\nExpands to: Constant Corelib.Init.Nat.testbit\nDeclared in library Corelib.Init.Nat, line 407, characters 9-16"
      },
      {
        "kername": "Corelib.Init.Nat.of_num_uint",
        "about": "Nat.of_num_uint : Number.uint -> nat\n\nNat.of_num_uint is not universe polymorphic\nArguments Nat.of_num_uint d\nNat.of_num_uint is transparent\nExpands to: Constant Corelib.Init.Nat.of_num_uint\nDeclared in library Corelib.Init.Nat, line 215, characters 11-22"
      },
      {
        "kername": "Corelib.Lists.ListDef.repeat",
        "about": "repeat : forall [A : Type], A -> nat -> list A\n\nrepeat is not universe polymorphic\nArguments repeat [A]%_type_scope x n%_nat_scope\nrepeat is transparent\nExpands to: Constant Corelib.Lists.ListDef.repeat\nDeclared in library Corelib.Lists.ListDef, line 54, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.sqrt_iter",
        "about": "Nat.sqrt_iter : nat -> nat -> nat -> nat -> nat\n\nNat.sqrt_iter is not universe polymorphic\nArguments Nat.sqrt_iter (k p q r)%_nat_scope\nNat.sqrt_iter is transparent\nExpands to: Constant Corelib.Init.Nat.sqrt_iter\nDeclared in library Corelib.Init.Nat, line 331, characters 9-18"
      },
      {
        "kername": "Corelib.Init.Nat.log2_iter",
        "about": "Nat.log2_iter : nat -> nat -> nat -> nat -> nat\n\nNat.log2_iter is not universe polymorphic\nArguments Nat.log2_iter (k p q r)%_nat_scope\nNat.log2_iter is transparent\nExpands to: Constant Corelib.Init.Nat.log2_iter\nDeclared in library Corelib.Init.Nat, line 375, characters 9-18"
      },
      {
        "kername": "Corelib.Lists.ListDef.firstn",
        "about": "firstn : forall [A : Type], nat -> list A -> list A\n\nfirstn is not universe polymorphic\nArguments firstn [A]%_type_scope n%_nat_scope l%_list_scope\nfirstn is transparent\nExpands to: Constant Corelib.Lists.ListDef.firstn\nDeclared in library Corelib.Lists.ListDef, line 84, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.to_int",
        "about": "Nat.to_int : nat -> Decimal.signed_int\n\nNat.to_int is not universe polymorphic\nArguments Nat.to_int n%_nat_scope\nNat.to_int is transparent\nExpands to: Constant Corelib.Init.Nat.to_int\nDeclared in library Corelib.Init.Nat, line 261, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.square",
        "about": "Nat.square : nat -> nat\n\nNat.square is not universe polymorphic\nArguments Nat.square n%_nat_scope\nNat.square is transparent\nExpands to: Constant Corelib.Init.Nat.square\nDeclared in library Corelib.Init.Nat, line 314, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.shiftr",
        "about": "Nat.shiftr : (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n\n\nNat.shiftr is not universe polymorphic\nArguments Nat.shiftr (a n)%_nat_scope\nNat.shiftr is transparent\nExpands to: Constant Corelib.Init.Nat.shiftr\nDeclared in library Corelib.Init.Nat, line 414, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.shiftl",
        "about": "Nat.shiftl : (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n\n\nNat.shiftl is not universe polymorphic\nArguments Nat.shiftl (a n)%_nat_scope\nNat.shiftl is transparent\nExpands to: Constant Corelib.Init.Nat.shiftl\nDeclared in library Corelib.Init.Nat, line 413, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.of_int",
        "about": "Nat.of_int : Decimal.signed_int -> option nat\n\nNat.of_int is not universe polymorphic\nArguments Nat.of_int d%_dec_int_scope\nNat.of_int is transparent\nExpands to: Constant Corelib.Init.Nat.of_int\nDeclared in library Corelib.Init.Nat, line 243, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.modulo",
        "about": "Nat.modulo : nat -> nat -> nat\n\nNat.modulo is not universe polymorphic\nArguments Nat.modulo (x y)%_nat_scope\nNat.modulo is transparent\nExpands to: Constant Corelib.Init.Nat.modulo\nDeclared in library Corelib.Init.Nat, line 289, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.double",
        "about": "Nat.double : nat -> nat\n\nNat.double is not universe polymorphic\nArguments Nat.double n%_nat_scope\nNat.double is transparent\nExpands to: Constant Corelib.Init.Nat.double\nDeclared in library Corelib.Init.Nat, line 57, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Nat.divmod",
        "about": "Nat.divmod : nat -> nat -> nat -> nat -> nat * nat\n\nNat.divmod is not universe polymorphic\nArguments Nat.divmod (x y q u)%_nat_scope\nNat.divmod is transparent\nExpands to: Constant Corelib.Init.Nat.divmod\nDeclared in library Corelib.Init.Nat, line 274, characters 9-15"
      },
      {
        "kername": "Corelib.Init.Nat.tail_addmul",
        "about": "Nat.tail_addmul : nat -> nat -> nat -> nat\n\nNat.tail_addmul is not universe polymorphic\nArguments Nat.tail_addmul (r n m)%_nat_scope\nNat.tail_addmul is transparent\nExpands to: Constant Corelib.Init.Nat.tail_addmul\nDeclared in library Corelib.Init.Nat, line 161, characters 9-20"
      },
      {
        "kername": "Corelib.Init.Nat.of_uint",
        "about": "Nat.of_uint : Decimal.uint -> nat\n\nNat.of_uint is not universe polymorphic\nArguments Nat.of_uint d%_dec_uint_scope\nNat.of_uint is transparent\nExpands to: Constant Corelib.Init.Nat.of_uint\nDeclared in library Corelib.Init.Nat, line 188, characters 11-18"
      },
      {
        "kername": "Corelib.Init.Nat.tail_mul",
        "about": "Nat.tail_mul : nat -> nat -> nat\n\nNat.tail_mul is not universe polymorphic\nArguments Nat.tail_mul (n m)%_nat_scope\nNat.tail_mul is transparent\nExpands to: Constant Corelib.Init.Nat.tail_mul\nDeclared in library Corelib.Init.Nat, line 167, characters 11-19"
      },
      {
        "kername": "Corelib.Init.Nat.tail_add",
        "about": "Nat.tail_add : nat -> nat -> nat\n\nNat.tail_add is not universe polymorphic\nArguments Nat.tail_add (n m)%_nat_scope\nNat.tail_add is transparent\nExpands to: Constant Corelib.Init.Nat.tail_add\nDeclared in library Corelib.Init.Nat, line 153, characters 9-17"
      },
      {
        "kername": "Corelib.Init.Nat.to_num_uint",
        "about": "Nat.to_num_uint : nat -> Number.uint\n\nNat.to_num_uint is not universe polymorphic\nArguments Nat.to_num_uint n%_nat_scope\nNat.to_num_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_num_uint\nDeclared in library Corelib.Init.Nat, line 239, characters 11-22"
      },
      {
        "kername": "Corelib.Lists.ListDef.skipn",
        "about": "skipn : forall [A : Type], nat -> list A -> list A\n\nskipn is not universe polymorphic\nArguments skipn [A]%_type_scope n%_nat_scope l%_list_scope\nskipn is transparent\nExpands to: Constant Corelib.Lists.ListDef.skipn\nDeclared in library Corelib.Lists.ListDef, line 93, characters 11-16"
      },
      {
        "kername": "Corelib.Lists.ListDef.seq",
        "about": "seq : nat -> nat -> list nat\n\nseq is not universe polymorphic\nArguments seq (start len)%_nat_scope\nseq is transparent\nExpands to: Constant Corelib.Lists.ListDef.seq\nDeclared in library Corelib.Lists.ListDef, line 43, characters 11-14"
      },
      {
        "kername": "Corelib.Lists.ListDef.nth",
        "about": "nth : forall [A : Type], nat -> list A -> A -> A\n\nnth is not universe polymorphic\nArguments nth [A]%_type_scope n%_nat_scope l%_list_scope default\nnth is transparent\nExpands to: Constant Corelib.Lists.ListDef.nth\nDeclared in library Corelib.Lists.ListDef, line 70, characters 11-14"
      },
      {
        "kername": "Corelib.Lists.ListDef.map",
        "about": "map : forall [A B : Type], (A -> B) -> list A -> list B\n\nmap is not universe polymorphic\nArguments map [A B]%_type_scope f%_function_scope l%_list_scope\nmap is transparent\nExpands to: Constant Corelib.Lists.ListDef.map\nDeclared in library Corelib.Lists.ListDef, line 30, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.ldiff",
        "about": "Nat.ldiff : nat -> nat -> nat\n\nNat.ldiff is not universe polymorphic\nArguments Nat.ldiff (a b)%_nat_scope\nNat.ldiff is transparent\nExpands to: Constant Corelib.Init.Nat.ldiff\nDeclared in library Corelib.Init.Nat, line 426, characters 11-16"
      },
      {
        "kername": "Corelib.Lists.ListDef.Forall_ind",
        "about": "Forall_ind :\nforall [A : Type] [P : A -> Prop] (P0 : list A -> Prop),\nP0 nil ->\n(forall (x : A) (l : list A), P x -> Forall P l -> P0 l -> P0 (x :: l)) ->\nforall [l : list A], Forall P l -> P0 l\n\nForall_ind is not universe polymorphic\nArguments Forall_ind [A]%_type_scope [P]%_function_scope \n  P%_function_scope f f0%_function_scope [l]%_list_scope \n  f\nForall_ind is transparent\nExpands to: Constant Corelib.Lists.ListDef.Forall_ind\nDeclared in library Corelib.Lists.ListDef, line 114, characters 4-142"
      },
      {
        "kername": "Corelib.Init.Nat.to_little_uint",
        "about": "Nat.to_little_uint : nat -> Decimal.uint -> Decimal.uint\n\nNat.to_little_uint is not universe polymorphic\nArguments Nat.to_little_uint n%_nat_scope acc\nNat.to_little_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_little_uint\nDeclared in library Corelib.Init.Nat, line 221, characters 9-23"
      },
      {
        "kername": "Corelib.Init.Nat.zero",
        "about": "Nat.zero : nat\n\nNat.zero is not universe polymorphic\nNat.zero is transparent\nExpands to: Constant Corelib.Init.Nat.zero\nDeclared in library Corelib.Init.Nat, line 31, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.succ",
        "about": "Nat.succ : nat -> nat\n\nNat.succ is not universe polymorphic\nArguments Nat.succ _%_nat_scope\nNat.succ is transparent\nExpands to: Constant Corelib.Init.Nat.succ\nDeclared in library Corelib.Init.Nat, line 37, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.sqrt",
        "about": "Nat.sqrt : nat -> nat\n\nNat.sqrt is not universe polymorphic\nArguments Nat.sqrt n%_nat_scope\nNat.sqrt is transparent\nExpands to: Constant Corelib.Init.Nat.sqrt\nDeclared in library Corelib.Init.Nat, line 340, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.pred",
        "about": "Nat.pred : nat -> nat\n\nNat.pred is not universe polymorphic\nArguments Nat.pred n%_nat_scope\nNat.pred is transparent\nExpands to: Constant Corelib.Init.Nat.pred\nDeclared in library Corelib.Init.Nat, line 39, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.lxor",
        "about": "Nat.lxor : nat -> nat -> nat\n\nNat.lxor is not universe polymorphic\nArguments Nat.lxor (a b)%_nat_scope\nNat.lxor is transparent\nExpands to: Constant Corelib.Init.Nat.lxor\nDeclared in library Corelib.Init.Nat, line 427, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.log2",
        "about": "Nat.log2 : nat -> nat\n\nNat.log2 is not universe polymorphic\nArguments Nat.log2 n%_nat_scope\nNat.log2 is transparent\nExpands to: Constant Corelib.Init.Nat.log2\nDeclared in library Corelib.Init.Nat, line 384, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.land",
        "about": "Nat.land : nat -> nat -> nat\n\nNat.land is not universe polymorphic\nArguments Nat.land (a b)%_nat_scope\nNat.land is transparent\nExpands to: Constant Corelib.Init.Nat.land\nDeclared in library Corelib.Init.Nat, line 424, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.iter",
        "about": "Nat.iter : nat -> forall {A : Type}, (A -> A) -> A -> A\n\nNat.iter is not universe polymorphic\nArguments Nat.iter n%_nat_scope {A}%_type_scope f%_function_scope x\nNat.iter is transparent\nExpands to: Constant Corelib.Init.Nat.iter\nDeclared in library Corelib.Init.Nat, line 388, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Nat.even",
        "about": "Nat.even : nat -> bool\n\nNat.even is not universe polymorphic\nArguments Nat.even n%_nat_scope\nNat.even is transparent\nExpands to: Constant Corelib.Init.Nat.even\nDeclared in library Corelib.Init.Nat, line 132, characters 9-13"
      },
      {
        "kername": "Corelib.Init.Nat.div2",
        "about": "Nat.div2 : nat -> nat\n\nNat.div2 is not universe polymorphic\nArguments Nat.div2 n%_nat_scope\nNat.div2 is transparent\nExpands to: Constant Corelib.Init.Nat.div2\nDeclared in library Corelib.Init.Nat, line 400, characters 9-13"
      },
      {
        "kername": "Corelib.Init.Nat.two",
        "about": "Nat.two : nat\n\nNat.two is not universe polymorphic\nNat.two is transparent\nExpands to: Constant Corelib.Init.Nat.two\nDeclared in library Corelib.Init.Nat, line 33, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.sub",
        "about": "Nat.sub : nat -> nat -> nat\n\nNat.sub is not universe polymorphic\nArguments Nat.sub (n m)%_nat_scope\nNat.sub is transparent\nExpands to: Constant Corelib.Init.Nat.sub\nDeclared in library Corelib.Init.Nat, line 71, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.pow",
        "about": "Nat.pow : nat -> nat -> nat\n\nNat.pow is not universe polymorphic\nArguments Nat.pow (n m)%_nat_scope\nNat.pow is transparent\nExpands to: Constant Corelib.Init.Nat.pow\nDeclared in library Corelib.Init.Nat, line 143, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.one",
        "about": "Nat.one : nat\n\nNat.one is not universe polymorphic\nNat.one is transparent\nExpands to: Constant Corelib.Init.Nat.one\nDeclared in library Corelib.Init.Nat, line 32, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.odd",
        "about": "Nat.odd : nat -> bool\n\nNat.odd is not universe polymorphic\nArguments Nat.odd n%_nat_scope\nNat.odd is transparent\nExpands to: Constant Corelib.Init.Nat.odd\nDeclared in library Corelib.Init.Nat, line 139, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.mul",
        "about": "Nat.mul : nat -> nat -> nat\n\nNat.mul is not universe polymorphic\nArguments Nat.mul (n m)%_nat_scope\nNat.mul is transparent\nExpands to: Constant Corelib.Init.Nat.mul\nDeclared in library Corelib.Init.Nat, line 59, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.min",
        "about": "Nat.min : nat -> nat -> nat\n\nNat.min is not universe polymorphic\nArguments Nat.min (n m)%_nat_scope\nNat.min is transparent\nExpands to: Constant Corelib.Init.Nat.min\nDeclared in library Corelib.Init.Nat, line 123, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.max",
        "about": "Nat.max : nat -> nat -> nat\n\nNat.max is not universe polymorphic\nArguments Nat.max (n m)%_nat_scope\nNat.max is transparent\nExpands to: Constant Corelib.Init.Nat.max\nDeclared in library Corelib.Init.Nat, line 116, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.ltb",
        "about": "Nat.ltb : nat -> nat -> bool\n\nNat.ltb is not universe polymorphic\nArguments Nat.ltb (n m)%_nat_scope\nNat.ltb is transparent\nExpands to: Constant Corelib.Init.Nat.ltb\nDeclared in library Corelib.Init.Nat, line 98, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.lor",
        "about": "Nat.lor : nat -> nat -> nat\n\nNat.lor is not universe polymorphic\nArguments Nat.lor (a b)%_nat_scope\nNat.lor is transparent\nExpands to: Constant Corelib.Init.Nat.lor\nDeclared in library Corelib.Init.Nat, line 425, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.leb",
        "about": "Nat.leb : nat -> nat -> bool\n\nNat.leb is not universe polymorphic\nArguments Nat.leb (n m)%_nat_scope\nNat.leb is transparent\nExpands to: Constant Corelib.Init.Nat.leb\nDeclared in library Corelib.Init.Nat, line 91, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.gcd",
        "about": "Nat.gcd : nat -> nat -> nat\n\nNat.gcd is not universe polymorphic\nArguments Nat.gcd (a b)%_nat_scope\nNat.gcd is transparent\nExpands to: Constant Corelib.Init.Nat.gcd\nDeclared in library Corelib.Init.Nat, line 306, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.eqb",
        "about": "Nat.eqb : nat -> nat -> bool\n\nNat.eqb is not universe polymorphic\nArguments Nat.eqb (n m)%_nat_scope\nNat.eqb is transparent\nExpands to: Constant Corelib.Init.Nat.eqb\nDeclared in library Corelib.Init.Nat, line 83, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.div",
        "about": "Nat.div : nat -> nat -> nat\n\nNat.div is not universe polymorphic\nArguments Nat.div (x y)%_nat_scope\nNat.div is transparent\nExpands to: Constant Corelib.Init.Nat.div\nDeclared in library Corelib.Init.Nat, line 283, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Nat.add",
        "about": "Nat.add : nat -> nat -> nat\n\nNat.add is not universe polymorphic\nArguments Nat.add (n m)%_nat_scope\nNat.add is transparent\nExpands to: Constant Corelib.Init.Nat.add\nDeclared in library Corelib.Init.Nat, line 47, characters 9-12"
      },
      {
        "kername": "Corelib.Init.Nat.t",
        "about": "Nat.t : Set\n\nNat.t is not universe polymorphic\nNat.t is transparent\nExpands to: Constant Corelib.Init.Nat.t\nDeclared in library Corelib.Init.Nat, line 23, characters 11-12"
      },
      {
        "kername": "Corelib.Init.Nat.of_num_int",
        "about": "Nat.of_num_int : Number.signed_int -> option nat\n\nNat.of_num_int is not universe polymorphic\nArguments Nat.of_num_int d\nNat.of_num_int is transparent\nExpands to: Constant Corelib.Init.Nat.of_num_int\nDeclared in library Corelib.Init.Nat, line 255, characters 11-21"
      },
      {
        "kername": "Corelib.Lists.ListDef.list_compare",
        "about": "list_compare :\nforall [A : Type], (A -> A -> comparison) -> list A -> list A -> comparison\n\nlist_compare is not universe polymorphic\nArguments list_compare [A]%_type_scope cmp%_function_scope\n  (xs ys)%_list_scope\nlist_compare is transparent\nExpands to: Constant Corelib.Lists.ListDef.list_compare\nDeclared in library Corelib.Lists.ListDef, line 131, characters 11-23"
      },
      {
        "kername": "Corelib.Init.Nat.to_num_int",
        "about": "Nat.to_num_int : nat -> Number.signed_int\n\nNat.to_num_int is not universe polymorphic\nArguments Nat.to_num_int n%_nat_scope\nNat.to_num_int is transparent\nExpands to: Constant Corelib.Init.Nat.to_num_int\nDeclared in library Corelib.Init.Nat, line 265, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Nat.to_num_hex_uint",
        "about": "Nat.to_num_hex_uint : nat -> Number.uint\n\nNat.to_num_hex_uint is not universe polymorphic\nArguments Nat.to_num_hex_uint n%_nat_scope\nNat.to_num_hex_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_num_hex_uint\nDeclared in library Corelib.Init.Nat, line 241, characters 11-26"
      },
      {
        "kername": "Corelib.Init.Nat.to_little_hex_uint",
        "about": "Nat.to_little_hex_uint : nat -> Hexadecimal.uint -> Hexadecimal.uint\n\nNat.to_little_hex_uint is not universe polymorphic\nArguments Nat.to_little_hex_uint n%_nat_scope acc\nNat.to_little_hex_uint is transparent\nExpands to: Constant Corelib.Init.Nat.to_little_hex_uint\nDeclared in library Corelib.Init.Nat, line 230, characters 9-27"
      }
    ],
    "inductives": [
      {
        "kername": "Corelib.Lists.ListDef.Forall",
        "print": "Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=\n    Forall_nil : Forall P nil\n  | Forall_cons : forall (x : A) (l : list A),\n                  P x -> Forall P l -> Forall P (x :: l).\n  \n  Arguments Forall [A]%_type_scope P%_function_scope _%_list_scope\n  Arguments Forall_nil [A]%_type_scope P%_function_scope\n  Arguments Forall_cons [A]%_type_scope [P]%_function_scope \n    x [l]%_list_scope _ _",
        "about": [
          "Forall : forall [A : Type], (A -> Prop) -> list A -> Prop\n\nForall is not universe polymorphic\nForall may only be eliminated to produce values whose type is SProp or Prop.\nArguments Forall [A]%_type_scope P%_function_scope _%_list_scope\nExpands to: Inductive Corelib.Lists.ListDef.Forall\nDeclared in library Corelib.Lists.ListDef, line 114, characters 14-20"
        ]
      }
    ]
  }
