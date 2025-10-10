Inductive my_nat : Set := MyO | MyS (_ : my_nat).

Fixpoint my_plus (a b : my_nat) : my_nat :=
  match a with
  | MyO => b
  | MyS a => my_plus a (MyS b)
  end.
