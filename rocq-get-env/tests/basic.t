  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.get_env.plugin.
  > Require Import Corelib.Lists.ListDef.
  > Print JSON Environment Corelib.Init.Nat Corelib.Lists Corelib.Init.Decimal.
  > EOF

  $ coqc test.v
  {
    "constants": [
      {
        "kername": "Corelib.Init.Decimal.revapp",
        "about": "Decimal.revapp : Decimal.uint -> Decimal.uint -> Decimal.uint\n\nDecimal.revapp is not universe polymorphic\nArguments Decimal.revapp (d d')%_dec_uint_scope\nDecimal.revapp is transparent\nExpands to: Constant Corelib.Init.Decimal.revapp\nDeclared in library Corelib.Init.Decimal, line 135, characters 9-15"
      },
      {
        "kername": "Corelib.Init.Decimal.uint_rec",
        "about": "Decimal.uint_rec :\nforall P : Decimal.uint -> Set,\nP Decimal.Nil ->\n(forall u : Decimal.uint, P u -> P (Decimal.D0 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D1 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D2 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D3 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D4 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D5 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D6 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D7 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D8 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D9 u)) ->\nforall u : Decimal.uint, P u\n\nDecimal.uint_rec is not universe polymorphic\nArguments Decimal.uint_rec P%_function_scope f\n  (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9)%_function_scope \n  u\nDecimal.uint_rec is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_rec\nDeclared in library Corelib.Init.Decimal, line 24, characters 0-175"
      },
      {
        "kername": "Corelib.Init.Decimal.uint_ind",
        "about": "Decimal.uint_ind :\nforall P : Decimal.uint -> Prop,\nP Decimal.Nil ->\n(forall u : Decimal.uint, P u -> P (Decimal.D0 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D1 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D2 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D3 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D4 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D5 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D6 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D7 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D8 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D9 u)) ->\nforall u : Decimal.uint, P u\n\nDecimal.uint_ind is not universe polymorphic\nArguments Decimal.uint_ind P%_function_scope f\n  (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9)%_function_scope \n  u\nDecimal.uint_ind is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_ind\nDeclared in library Corelib.Init.Decimal, line 24, characters 0-175"
      },
      {
        "kername": "Corelib.Init.Decimal.uint_beq",
        "about": "Decimal.uint_beq : Decimal.uint -> Decimal.uint -> bool\n\nDecimal.uint_beq is not universe polymorphic\nArguments Decimal.uint_beq X Y\nDecimal.uint_beq is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_beq\nDeclared in library Corelib.Init.Decimal, line 57, characters 0-25"
      },
      {
        "kername": "Corelib.Init.Decimal.nztail",
        "about": "Decimal.nztail : Decimal.uint -> Decimal.uint * nat\n\nDecimal.nztail is not universe polymorphic\nArguments Decimal.nztail d%_dec_uint_scope\nDecimal.nztail is transparent\nExpands to: Constant Corelib.Init.Decimal.nztail\nDeclared in library Corelib.Init.Decimal, line 160, characters 11-17"
      },
      {
        "kername": "Corelib.Init.Decimal.nzhead",
        "about": "Decimal.nzhead : Decimal.uint -> Decimal.uint\n\nDecimal.nzhead is not universe polymorphic\nArguments Decimal.nzhead d%_dec_uint_scope\nDecimal.nzhead is transparent\nExpands to: Constant Corelib.Init.Decimal.nzhead\nDeclared in library Corelib.Init.Decimal, line 91, characters 9-15"
      },
      {
        "kername": "Corelib.Init.Nat.of_hex_int",
        "about": "Nat.of_hex_int : Hexadecimal.signed_int -> option nat\n\nNat.of_hex_int is not universe polymorphic\nArguments Nat.of_hex_int d%_hex_int_scope\nNat.of_hex_int is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_int\nDeclared in library Corelib.Init.Nat, line 249, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Nat.of_hex_uint",
        "about": "Nat.of_hex_uint : Hexadecimal.uint -> nat\n\nNat.of_hex_uint is not universe polymorphic\nArguments Nat.of_hex_uint d%_hex_uint_scope\nNat.of_hex_uint is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_uint\nDeclared in library Corelib.Init.Nat, line 213, characters 11-22"
      },
      {
        "kername": "Corelib.Init.Decimal.Little.succ_double",
        "about": "Decimal.Little.succ_double : Decimal.uint -> Decimal.uint\n\nDecimal.Little.succ_double is not universe polymorphic\nArguments Decimal.Little.succ_double d%_dec_uint_scope\nDecimal.Little.succ_double is transparent\nExpands to: Constant Corelib.Init.Decimal.Little.succ_double\nDeclared in library Corelib.Init.Decimal, line 241, characters 5-16"
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
        "kername": "Corelib.Init.Decimal.uint_eq_dec",
        "about": "Decimal.uint_eq_dec : forall x y : Decimal.uint, {x = y} + {x <> y}\n\nDecimal.uint_eq_dec is not universe polymorphic\nArguments Decimal.uint_eq_dec x y\nDecimal.uint_eq_dec is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_eq_dec\nDeclared in library Corelib.Init.Decimal, line 57, characters 0-25"
      },
      {
        "kername": "Corelib.Init.Nat.compare",
        "about": "Nat.compare : nat -> nat -> comparison\n\nNat.compare is not universe polymorphic\nArguments Nat.compare (n m)%_nat_scope\nNat.compare is transparent\nExpands to: Constant Corelib.Init.Nat.compare\nDeclared in library Corelib.Init.Nat, line 104, characters 9-16"
      },
      {
        "kername": "Corelib.Init.Decimal.int_of_int",
        "about": "Decimal.int_of_int : Decimal.signed_int -> Decimal.signed_int\n\nDecimal.int_of_int is not universe polymorphic\nArguments Decimal.int_of_int i%_dec_int_scope\nDecimal.int_of_int is transparent\nExpands to: Constant Corelib.Init.Decimal.int_of_int\nDeclared in library Corelib.Init.Decimal, line 262, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Decimal.uint_sind",
        "about": "Decimal.uint_sind :\nforall P : Decimal.uint -> SProp,\nP Decimal.Nil ->\n(forall u : Decimal.uint, P u -> P (Decimal.D0 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D1 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D2 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D3 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D4 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D5 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D6 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D7 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D8 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D9 u)) ->\nforall u : Decimal.uint, P u\n\nDecimal.uint_sind is not universe polymorphic\nArguments Decimal.uint_sind P%_function_scope f\n  (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9)%_function_scope \n  u\nDecimal.uint_sind is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_sind\nDeclared in library Corelib.Init.Decimal, line 24, characters 0-175"
      },
      {
        "kername": "Corelib.Init.Decimal.uint_rect",
        "about": "Decimal.uint_rect :\nforall P : Decimal.uint -> Type,\nP Decimal.Nil ->\n(forall u : Decimal.uint, P u -> P (Decimal.D0 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D1 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D2 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D3 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D4 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D5 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D6 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D7 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D8 u)) ->\n(forall u : Decimal.uint, P u -> P (Decimal.D9 u)) ->\nforall u : Decimal.uint, P u\n\nDecimal.uint_rect is not universe polymorphic\nArguments Decimal.uint_rect P%_function_scope f\n  (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9)%_function_scope \n  u\nDecimal.uint_rect is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_rect\nDeclared in library Corelib.Init.Decimal, line 24, characters 0-175"
      },
      {
        "kername": "Corelib.Init.Nat.bitwise",
        "about": "Nat.bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat\n\nNat.bitwise is not universe polymorphic\nArguments Nat.bitwise op%_function_scope (n a b)%_nat_scope\nNat.bitwise is transparent\nExpands to: Constant Corelib.Init.Nat.bitwise\nDeclared in library Corelib.Init.Nat, line 416, characters 9-16"
      },
      {
        "kername": "Corelib.Init.Decimal.Little.double",
        "about": "Decimal.Little.double : Decimal.uint -> Decimal.uint\n\nDecimal.Little.double is not universe polymorphic\nArguments Decimal.Little.double d%_dec_uint_scope\nDecimal.Little.double is transparent\nExpands to: Constant Corelib.Init.Decimal.Little.double\nDeclared in library Corelib.Init.Decimal, line 226, characters 9-15"
      },
      {
        "kername": "Corelib.Init.Nat.of_hex_uint_acc",
        "about": "Nat.of_hex_uint_acc : Hexadecimal.uint -> nat -> nat\n\nNat.of_hex_uint_acc is not universe polymorphic\nArguments Nat.of_hex_uint_acc d acc%_nat_scope\nNat.of_hex_uint_acc is transparent\nExpands to: Constant Corelib.Init.Nat.of_hex_uint_acc\nDeclared in library Corelib.Init.Nat, line 192, characters 9-24"
      },
      {
        "kername": "Corelib.Init.Decimal.unorm",
        "about": "Decimal.unorm : Decimal.uint -> Decimal.uint\n\nDecimal.unorm is not universe polymorphic\nArguments Decimal.unorm d%_dec_uint_scope\nDecimal.unorm is transparent\nExpands to: Constant Corelib.Init.Decimal.unorm\nDeclared in library Corelib.Init.Decimal, line 99, characters 11-16"
      },
      {
        "kername": "Corelib.Init.Decimal.internal_uint_dec_lb",
        "about": "Decimal.internal_uint_dec_lb :\nforall x : Decimal.uint,\n(fun x0 : Decimal.uint =>\n forall y : Decimal.uint, x0 = y -> Decimal.uint_beq x0 y = true) x\n\nDecimal.internal_uint_dec_lb is not universe polymorphic\nArguments Decimal.internal_uint_dec_lb x y _\nDecimal.internal_uint_dec_lb is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_uint_dec_lb\nDeclared in library Corelib.Init.Decimal, line 57, characters 0-25"
      },
      {
        "kername": "Corelib.Init.Decimal.internal_uint_dec_bl",
        "about": "Decimal.internal_uint_dec_bl :\nforall x : Decimal.uint,\n(fun x0 : Decimal.uint =>\n forall y : Decimal.uint, Decimal.uint_beq x0 y = true -> x0 = y) x\n\nDecimal.internal_uint_dec_bl is not universe polymorphic\nArguments Decimal.internal_uint_dec_bl x y _\nDecimal.internal_uint_dec_bl is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_uint_dec_bl\nDeclared in library Corelib.Init.Decimal, line 57, characters 0-25"
      },
      {
        "kername": "Corelib.Init.Decimal.norm",
        "about": "Decimal.norm : Decimal.signed_int -> Decimal.signed_int\n\nDecimal.norm is not universe polymorphic\nArguments Decimal.norm d%_dec_int_scope\nDecimal.norm is transparent\nExpands to: Constant Corelib.Init.Decimal.norm\nDeclared in library Corelib.Init.Decimal, line 107, characters 11-15"
      },
      {
        "kername": "Corelib.Init.Decimal.rev",
        "about": "Decimal.rev : Decimal.uint -> Decimal.uint\n\nDecimal.rev is not universe polymorphic\nArguments Decimal.rev d%_dec_uint_scope\nDecimal.rev is transparent\nExpands to: Constant Corelib.Init.Decimal.rev\nDeclared in library Corelib.Init.Decimal, line 150, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Decimal.opp",
        "about": "Decimal.opp : Decimal.signed_int -> Decimal.signed_int\n\nDecimal.opp is not universe polymorphic\nArguments Decimal.opp d%_dec_int_scope\nDecimal.opp is transparent\nExpands to: Constant Corelib.Init.Decimal.opp\nDeclared in library Corelib.Init.Decimal, line 120, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Decimal.app",
        "about": "Decimal.app : Decimal.uint -> Decimal.uint -> Decimal.uint\n\nDecimal.app is not universe polymorphic\nArguments Decimal.app (d d')%_dec_uint_scope\nDecimal.app is transparent\nExpands to: Constant Corelib.Init.Decimal.app\nDeclared in library Corelib.Init.Decimal, line 152, characters 11-14"
      },
      {
        "kername": "Corelib.Init.Decimal.abs",
        "about": "Decimal.abs : Decimal.signed_int -> Decimal.uint\n\nDecimal.abs is not universe polymorphic\nArguments Decimal.abs d%_dec_int_scope\nDecimal.abs is transparent\nExpands to: Constant Corelib.Init.Decimal.abs\nDeclared in library Corelib.Init.Decimal, line 126, characters 11-14"
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
        "kername": "Corelib.Init.Decimal.del_tail",
        "about": "Decimal.del_tail : nat -> Decimal.uint -> Decimal.uint\n\nDecimal.del_tail is not universe polymorphic\nArguments Decimal.del_tail n%_nat_scope d%_dec_uint_scope\nDecimal.del_tail is transparent\nExpands to: Constant Corelib.Init.Decimal.del_tail\nDeclared in library Corelib.Init.Decimal, line 197, characters 11-19"
      },
      {
        "kername": "Corelib.Init.Decimal.del_head",
        "about": "Decimal.del_head : nat -> Decimal.uint -> Decimal.uint\n\nDecimal.del_head is not universe polymorphic\nArguments Decimal.del_head n%_nat_scope d%_dec_uint_scope\nDecimal.del_head is transparent\nExpands to: Constant Corelib.Init.Decimal.del_head\nDeclared in library Corelib.Init.Decimal, line 177, characters 9-17"
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
        "kername": "Corelib.Init.Decimal.nb_digits",
        "about": "Decimal.nb_digits : Decimal.uint -> nat\n\nDecimal.nb_digits is not universe polymorphic\nArguments Decimal.nb_digits d%_dec_uint_scope\nDecimal.nb_digits is transparent\nExpands to: Constant Corelib.Init.Decimal.nb_digits\nDeclared in library Corelib.Init.Decimal, line 77, characters 9-18"
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
        "kername": "Corelib.Init.Decimal.Little.succ",
        "about": "Decimal.Little.succ : Decimal.uint -> Decimal.uint\n\nDecimal.Little.succ is not universe polymorphic\nArguments Decimal.Little.succ d%_dec_uint_scope\nDecimal.Little.succ is transparent\nExpands to: Constant Corelib.Init.Decimal.Little.succ\nDeclared in library Corelib.Init.Decimal, line 209, characters 9-13"
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
        "kername": "Corelib.Init.Decimal.uint_of_uint",
        "about": "Decimal.uint_of_uint : Decimal.uint -> Decimal.uint\n\nDecimal.uint_of_uint is not universe polymorphic\nArguments Decimal.uint_of_uint i%_dec_uint_scope\nDecimal.uint_of_uint is transparent\nExpands to: Constant Corelib.Init.Decimal.uint_of_uint\nDeclared in library Corelib.Init.Decimal, line 261, characters 11-23"
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
        "kername": "Corelib.Init.Decimal.internal_signed_int_dec_lb",
        "about": "Decimal.internal_signed_int_dec_lb :\nforall x y : Decimal.signed_int, x = y -> Decimal.signed_int_beq x y = true\n\nDecimal.internal_signed_int_dec_lb is not universe polymorphic\nArguments Decimal.internal_signed_int_dec_lb x y _\nDecimal.internal_signed_int_dec_lb is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_signed_int_dec_lb\nDeclared in library Corelib.Init.Decimal, line 58, characters 0-24"
      },
      {
        "kername": "Corelib.Init.Decimal.internal_signed_int_dec_bl",
        "about": "Decimal.internal_signed_int_dec_bl :\nforall x y : Decimal.signed_int, Decimal.signed_int_beq x y = true -> x = y\n\nDecimal.internal_signed_int_dec_bl is not universe polymorphic\nArguments Decimal.internal_signed_int_dec_bl x y _\nDecimal.internal_signed_int_dec_bl is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_signed_int_dec_bl\nDeclared in library Corelib.Init.Decimal, line 58, characters 0-24"
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
        "kername": "Corelib.Init.Decimal.nztail_int",
        "about": "Decimal.nztail_int : Decimal.signed_int -> Decimal.signed_int * nat\n\nDecimal.nztail_int is not universe polymorphic\nArguments Decimal.nztail_int d%_dec_int_scope\nDecimal.nztail_int is transparent\nExpands to: Constant Corelib.Init.Decimal.nztail_int\nDeclared in library Corelib.Init.Decimal, line 168, characters 11-21"
      },
      {
        "kername": "Corelib.Init.Nat.of_uint",
        "about": "Nat.of_uint : Decimal.uint -> nat\n\nNat.of_uint is not universe polymorphic\nArguments Nat.of_uint d%_dec_uint_scope\nNat.of_uint is transparent\nExpands to: Constant Corelib.Init.Nat.of_uint\nDeclared in library Corelib.Init.Nat, line 188, characters 11-18"
      },
      {
        "kername": "Corelib.Init.Decimal.decimal_eq_dec",
        "about": "Decimal.decimal_eq_dec : forall x y : Decimal.decimal, {x = y} + {x <> y}\n\nDecimal.decimal_eq_dec is not universe polymorphic\nArguments Decimal.decimal_eq_dec x y\nDecimal.decimal_eq_dec is transparent\nExpands to: Constant Corelib.Init.Decimal.decimal_eq_dec\nDeclared in library Corelib.Init.Decimal, line 59, characters 0-28"
      },
      {
        "kername": "Corelib.Init.Decimal.internal_decimal_dec_lb",
        "about": "Decimal.internal_decimal_dec_lb :\nforall x y : Decimal.decimal, x = y -> Decimal.decimal_beq x y = true\n\nDecimal.internal_decimal_dec_lb is not universe polymorphic\nArguments Decimal.internal_decimal_dec_lb x y _\nDecimal.internal_decimal_dec_lb is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_decimal_dec_lb\nDeclared in library Corelib.Init.Decimal, line 59, characters 0-28"
      },
      {
        "kername": "Corelib.Init.Decimal.internal_decimal_dec_bl",
        "about": "Decimal.internal_decimal_dec_bl :\nforall x y : Decimal.decimal, Decimal.decimal_beq x y = true -> x = y\n\nDecimal.internal_decimal_dec_bl is not universe polymorphic\nArguments Decimal.internal_decimal_dec_bl x y _\nDecimal.internal_decimal_dec_bl is transparent\nExpands to: Constant Corelib.Init.Decimal.internal_decimal_dec_bl\nDeclared in library Corelib.Init.Decimal, line 59, characters 0-28"
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
        "kername": "Corelib.Init.Decimal.signed_int_beq",
        "about": "Decimal.signed_int_beq : Decimal.signed_int -> Decimal.signed_int -> bool\n\nDecimal.signed_int_beq is not universe polymorphic\nArguments Decimal.signed_int_beq X Y\nDecimal.signed_int_beq is transparent\nExpands to: Constant Corelib.Init.Decimal.signed_int_beq\nDeclared in library Corelib.Init.Decimal, line 58, characters 0-24"
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
        "kername": "Corelib.Init.Decimal.del_head_int",
        "about": "Decimal.del_head_int : nat -> Decimal.signed_int -> Decimal.uint\n\nDecimal.del_head_int is not universe polymorphic\nArguments Decimal.del_head_int n%_nat_scope d%_dec_int_scope\nDecimal.del_head_int is transparent\nExpands to: Constant Corelib.Init.Decimal.del_head_int\nDeclared in library Corelib.Init.Decimal, line 188, characters 11-23"
      },
      {
        "kername": "Corelib.Init.Decimal.decimal_beq",
        "about": "Decimal.decimal_beq : Decimal.decimal -> Decimal.decimal -> bool\n\nDecimal.decimal_beq is not universe polymorphic\nArguments Decimal.decimal_beq X Y\nDecimal.decimal_beq is transparent\nExpands to: Constant Corelib.Init.Decimal.decimal_beq\nDeclared in library Corelib.Init.Decimal, line 59, characters 0-28"
      },
      {
        "kername": "Corelib.Init.Decimal.app_int",
        "about": "Decimal.app_int : Decimal.signed_int -> Decimal.uint -> Decimal.signed_int\n\nDecimal.app_int is not universe polymorphic\nArguments Decimal.app_int d1%_dec_int_scope d2%_dec_uint_scope\nDecimal.app_int is transparent\nExpands to: Constant Corelib.Init.Decimal.app_int\nDeclared in library Corelib.Init.Decimal, line 154, characters 11-18"
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
      },
      {
        "kername": "Corelib.Init.Decimal.signed_int_eq_dec",
        "about": "Decimal.signed_int_eq_dec :\nforall x y : Decimal.signed_int, {x = y} + {x <> y}\n\nDecimal.signed_int_eq_dec is not universe polymorphic\nArguments Decimal.signed_int_eq_dec x y\nDecimal.signed_int_eq_dec is transparent\nExpands to: Constant Corelib.Init.Decimal.signed_int_eq_dec\nDeclared in library Corelib.Init.Decimal, line 58, characters 0-24"
      },
      {
        "kername": "Corelib.Init.Decimal.del_tail_int",
        "about": "Decimal.del_tail_int : nat -> Decimal.signed_int -> Decimal.signed_int\n\nDecimal.del_tail_int is not universe polymorphic\nArguments Decimal.del_tail_int n%_nat_scope d%_dec_int_scope\nDecimal.del_tail_int is transparent\nExpands to: Constant Corelib.Init.Decimal.del_tail_int\nDeclared in library Corelib.Init.Decimal, line 199, characters 11-23"
      }
    ],
    "inductives": [
      {
        "kername": "Corelib.Init.Decimal.signed_int",
        "print": "Variant signed_int : Set :=\n    Pos : Decimal.uint -> Decimal.signed_int\n  | Neg : Decimal.uint -> Decimal.signed_int.\n  \n  Arguments Decimal.Pos d\n  Arguments Decimal.Neg d",
        "about": [
          "Decimal.signed_int : Set\n\nDecimal.signed_int is not universe polymorphic\nExpands to: Inductive Corelib.Init.Decimal.signed_int\nDeclared in library Corelib.Init.Decimal, line 45, characters 8-18"
        ]
      },
      {
        "kername": "Corelib.Init.Decimal.uint",
        "print": "Inductive uint : Set :=\n    Nil : Decimal.uint\n  | D0 : Decimal.uint -> Decimal.uint\n  | D1 : Decimal.uint -> Decimal.uint\n  | D2 : Decimal.uint -> Decimal.uint\n  | D3 : Decimal.uint -> Decimal.uint\n  | D4 : Decimal.uint -> Decimal.uint\n  | D5 : Decimal.uint -> Decimal.uint\n  | D6 : Decimal.uint -> Decimal.uint\n  | D7 : Decimal.uint -> Decimal.uint\n  | D8 : Decimal.uint -> Decimal.uint\n  | D9 : Decimal.uint -> Decimal.uint.",
        "about": [
          "Decimal.uint : Set\n\nDecimal.uint is not universe polymorphic\nExpands to: Inductive Corelib.Init.Decimal.uint\nDeclared in library Corelib.Init.Decimal, line 24, characters 10-14"
        ]
      },
      {
        "kername": "Corelib.Lists.ListDef.Forall",
        "print": "Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=\n    Forall_nil : Forall P nil\n  | Forall_cons : forall (x : A) (l : list A),\n                  P x -> Forall P l -> Forall P (x :: l).\n  \n  Arguments Forall [A]%_type_scope P%_function_scope _%_list_scope\n  Arguments Forall_nil [A]%_type_scope P%_function_scope\n  Arguments Forall_cons [A]%_type_scope [P]%_function_scope \n    x [l]%_list_scope _ _",
        "about": [
          "Forall : forall [A : Type], (A -> Prop) -> list A -> Prop\n\nForall is not universe polymorphic\nForall may only be eliminated to produce values whose type is SProp or Prop.\nArguments Forall [A]%_type_scope P%_function_scope _%_list_scope\nExpands to: Inductive Corelib.Lists.ListDef.Forall\nDeclared in library Corelib.Lists.ListDef, line 114, characters 14-20"
        ]
      },
      {
        "kername": "Corelib.Init.Decimal.decimal",
        "print": "Variant decimal : Set :=\n    Decimal : Decimal.signed_int -> Decimal.uint -> Decimal.decimal\n  | DecimalExp : Decimal.signed_int ->\n                 Decimal.uint -> Decimal.signed_int -> Decimal.decimal.\n  \n  Arguments Decimal.Decimal i f\n  Arguments Decimal.DecimalExp i f e",
        "about": [
          "Decimal.decimal : Set\n\nDecimal.decimal is not universe polymorphic\nExpands to: Inductive Corelib.Init.Decimal.decimal\nDeclared in library Corelib.Init.Decimal, line 53, characters 8-15"
        ]
      }
    ],
    "abbrevs": [
      {
        "full_path": "Corelib.Init.Decimal.internal_int_dec_lb",
        "print": "Notation Decimal.internal_int_dec_lb := Decimal.internal_signed_int_dec_lb\n  \n  Decimal.internal_signed_int_dec_lb =\n  fun x : Decimal.signed_int =>\n  match\n    x as s\n    return\n      (forall y : Decimal.signed_int,\n       s = y -> Decimal.signed_int_beq s y = true)\n  with\n  | Decimal.Pos d =>\n      (fun (d0 : Decimal.uint) (y : Decimal.signed_int) =>\n       match\n         y as s\n         return\n           (Decimal.Pos d0 = s ->\n            Decimal.signed_int_beq (Decimal.Pos d0) s = true)\n       with\n       | Decimal.Pos d1 =>\n           (fun (d2 : Decimal.uint) (Z : Decimal.Pos d0 = Decimal.Pos d2) =>\n            let H : d0 = d2 :=\n              f_equal\n                (fun e : Decimal.signed_int =>\n                 match e with\n                 | Decimal.Pos d3 => d3\n                 | Decimal.Neg _ => d0\n                 end)\n                Z\n              in\n            (fun H0 : d0 = d2 =>\n             (let H1 : d2 = d0 := eq_sym H0 in\n              eq_ind d2\n                (fun d3 : Decimal.uint => Decimal.uint_beq d3 d2 = true)\n                (Decimal.internal_uint_dec_lb d2 d2 eq_refl) d0 H1)\n             :\n             Decimal.signed_int_beq (Decimal.Pos d0) (Decimal.Pos d2) = true)\n              H)\n             d1\n       | Decimal.Neg d1 =>\n           (fun (d2 : Decimal.uint) (Z : Decimal.Pos d0 = Decimal.Neg d2) =>\n            let H : False :=\n              eq_ind (Decimal.Pos d0)\n                (fun e : Decimal.signed_int =>\n                 match e with\n                 | Decimal.Pos _ => True\n                 | Decimal.Neg _ => False\n                 end)\n                I (Decimal.Neg d2) Z\n              in\n            False_ind\n              (Decimal.signed_int_beq (Decimal.Pos d0) (Decimal.Neg d2) =\n               true)\n              H)\n             d1\n       end) d\n  | Decimal.Neg d =>\n      (fun (d0 : Decimal.uint) (y : Decimal.signed_int) =>\n       match\n         y as s\n         return\n           (Decimal.Neg d0 = s ->\n            Decimal.signed_int_beq (Decimal.Neg d0) s = true)\n       with\n       | Decimal.Pos d1 =>\n           (fun (d2 : Decimal.uint) (Z : Decimal.Neg d0 = Decimal.Pos d2) =>\n            let H : False :=\n              eq_ind (Decimal.Neg d0)\n                (fun e : Decimal.signed_int =>\n                 match e with\n                 | Decimal.Pos _ => False\n                 | Decimal.Neg _ => True\n                 end)\n                I (Decimal.Pos d2) Z\n              in\n            False_ind\n              (Decimal.signed_int_beq (Decimal.Neg d0) (Decimal.Pos d2) =\n               true)\n              H)\n             d1\n       | Decimal.Neg d1 =>\n           (fun (d2 : Decimal.uint) (Z : Decimal.Neg d0 = Decimal.Neg d2) =>\n            let H : d0 = d2 :=\n              f_equal\n                (fun e : Decimal.signed_int =>\n                 match e with\n                 | Decimal.Pos _ => d0\n                 | Decimal.Neg d3 => d3\n                 end)\n                Z\n              in\n            (fun H0 : d0 = d2 =>\n             (let H1 : d2 = d0 := eq_sym H0 in\n              eq_ind d2\n                (fun d3 : Decimal.uint => Decimal.uint_beq d3 d2 = true)\n                (Decimal.internal_uint_dec_lb d2 d2 eq_refl) d0 H1)\n             :\n             Decimal.signed_int_beq (Decimal.Neg d0) (Decimal.Neg d2) = true)\n              H)\n             d1\n       end) d\n  end\n       : forall x y : Decimal.signed_int,\n         x = y -> Decimal.signed_int_beq x y = true\n  \n  Arguments Decimal.internal_signed_int_dec_lb x y _"
      },
      {
        "full_path": "Corelib.Init.Decimal.internal_int_dec_bl",
        "print": "Notation Decimal.internal_int_dec_bl := Decimal.internal_signed_int_dec_bl\n  \n  Decimal.internal_signed_int_dec_bl =\n  fun x : Decimal.signed_int =>\n  match\n    x as s\n    return\n      (forall y : Decimal.signed_int,\n       Decimal.signed_int_beq s y = true -> s = y)\n  with\n  | Decimal.Pos d =>\n      (fun (d0 : Decimal.uint) (y : Decimal.signed_int) =>\n       match\n         y as s\n         return\n           (Decimal.signed_int_beq (Decimal.Pos d0) s = true ->\n            Decimal.Pos d0 = s)\n       with\n       | Decimal.Pos d1 =>\n           (fun (d2 : Decimal.uint)\n              (Z : Decimal.signed_int_beq (Decimal.Pos d0) (Decimal.Pos d2) =\n                   true) =>\n            let H : d0 = d2 := Decimal.internal_uint_dec_bl d0 d2 Z in\n            eq_ind d0\n              (fun d3 : Decimal.uint => Decimal.Pos d0 = Decimal.Pos d3)\n              eq_refl d2 H)\n             d1\n       | Decimal.Neg d1 =>\n           (fun (d2 : Decimal.uint)\n              (Z : Decimal.signed_int_beq (Decimal.Pos d0) (Decimal.Neg d2) =\n                   true) =>\n            let H : False :=\n              eq_ind\n                (Decimal.signed_int_beq (Decimal.Pos d0) (Decimal.Neg d2))\n                (fun e : bool => if e then False else True) I true Z\n              in\n            False_ind (Decimal.Pos d0 = Decimal.Neg d2) H) d1\n       end) d\n  | Decimal.Neg d =>\n      (fun (d0 : Decimal.uint) (y : Decimal.signed_int) =>\n       match\n         y as s\n         return\n           (Decimal.signed_int_beq (Decimal.Neg d0) s = true ->\n            Decimal.Neg d0 = s)\n       with\n       | Decimal.Pos d1 =>\n           (fun (d2 : Decimal.uint)\n              (Z : Decimal.signed_int_beq (Decimal.Neg d0) (Decimal.Pos d2) =\n                   true) =>\n            let H : False :=\n              eq_ind\n                (Decimal.signed_int_beq (Decimal.Neg d0) (Decimal.Pos d2))\n                (fun e : bool => if e then False else True) I true Z\n              in\n            False_ind (Decimal.Neg d0 = Decimal.Pos d2) H) d1\n       | Decimal.Neg d1 =>\n           (fun (d2 : Decimal.uint)\n              (Z : Decimal.signed_int_beq (Decimal.Neg d0) (Decimal.Neg d2) =\n                   true) =>\n            let H : d0 = d2 := Decimal.internal_uint_dec_bl d0 d2 Z in\n            eq_ind d0\n              (fun d3 : Decimal.uint => Decimal.Neg d0 = Decimal.Neg d3)\n              eq_refl d2 H)\n             d1\n       end) d\n  end\n       : forall x y : Decimal.signed_int,\n         Decimal.signed_int_beq x y = true -> x = y\n  \n  Arguments Decimal.internal_signed_int_dec_bl x y _"
      },
      {
        "full_path": "Corelib.Init.Decimal.int_eq_dec",
        "print": "Notation Decimal.int_eq_dec := Decimal.signed_int_eq_dec\n  \n  Decimal.signed_int_eq_dec =\n  fun x y : Decimal.signed_int =>\n  let H :=\n    let b := Decimal.signed_int_beq x y in\n    if b as b0 return ({b0 = true} + {b0 = false})\n    then left eq_refl\n    else right eq_refl in\n  match H with\n  | left e =>\n      (fun e0 : Decimal.signed_int_beq x y = true =>\n       left (Decimal.internal_signed_int_dec_bl x y e0)) e\n  | right e =>\n      (fun H0 : Decimal.signed_int_beq x y = false =>\n       right\n         ((fun H1 : x = y =>\n           eq_ind_r\n             (fun x0 : Decimal.signed_int =>\n              Decimal.signed_int_beq x0 y = false -> False)\n             (fun H2 : Decimal.signed_int_beq y y = false =>\n              let H3 : Decimal.signed_int_beq y y = true :=\n                Decimal.internal_signed_int_dec_lb y y eq_refl in\n              let H4 : false = true :=\n                eq_ind (Decimal.signed_int_beq y y)\n                  (fun b : bool => b = true) H3 false H2\n                in\n              let H5 : False :=\n                eq_ind false (fun e0 : bool => if e0 then False else True) I\n                  true H4\n                in\n              False_ind False H5)\n             H1 H0)\n          :\n          x <> y))\n        e\n  end\n       : forall x y : Decimal.signed_int, {x = y} + {x <> y}\n  \n  Arguments Decimal.signed_int_eq_dec x y"
      },
      {
        "full_path": "Corelib.Init.Decimal.zero",
        "print": "Notation Decimal.zero := (Decimal.D0 Decimal.Nil)"
      },
      {
        "full_path": "Corelib.Init.Decimal.int",
        "print": "Notation Decimal.int := Decimal.signed_int\n  \n  Variant signed_int : Set :=\n      Pos : Decimal.uint -> Decimal.signed_int\n    | Neg : Decimal.uint -> Decimal.signed_int.\n  \n  Arguments Decimal.Pos d\n  Arguments Decimal.Neg d"
      },
      {
        "full_path": "Corelib.Init.Decimal.int_beq",
        "print": "Notation Decimal.int_beq := Decimal.signed_int_beq\n  \n  Decimal.signed_int_beq =\n  fun X Y : Decimal.signed_int =>\n  match X with\n  | Decimal.Pos d =>\n      match Y with\n      | Decimal.Pos d0 => Decimal.uint_beq d d0\n      | Decimal.Neg _ => false\n      end\n  | Decimal.Neg d =>\n      match Y with\n      | Decimal.Pos _ => false\n      | Decimal.Neg d0 => Decimal.uint_beq d d0\n      end\n  end\n       : Decimal.signed_int -> Decimal.signed_int -> bool\n  \n  Arguments Decimal.signed_int_beq X Y"
      }
    ]
  }
