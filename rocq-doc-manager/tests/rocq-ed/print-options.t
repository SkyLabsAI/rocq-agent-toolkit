  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

Commands that used to auto-print context and goals are quiet by default.

  $ cat > print.v <<EOF
  > Definition a := 0.
  > Definition b := 1.
  > Definition c := 2.
  > EOF

  $ rocq-ed init print.v
  $ rocq-ed goto --print-context=1 --position-line-column 2:1 print.v
     1| Definition a := 0.
     2| <CURSOR>Definition b := 1.
     3| Definition c := 2.
  $ rocq-ed goto --position-line-column 1:1 print.v && echo "<NO OUTPUT: goto>"
  <NO OUTPUT: goto>
  $ rocq-ed steps --count-items=2 print.v && echo "<NO OUTPUT: steps>"
  <NO OUTPUT: steps>
  $ rocq-ed backwards --count-items=1 print.v && echo "<NO OUTPUT: backwards>"
  <NO OUTPUT: backwards>
  $ rocq-ed insert --text $'\nDefinition inserted := 42.' print.v && echo "<NO OUTPUT: insert>"
  <NO OUTPUT: insert>
  $ rocq-ed delete --count-items=1 print.v && echo "<NO OUTPUT: delete>"
  <NO OUTPUT: delete>
  $ rocq-ed stop print.v

--print-goals can be requested without printing context.

  $ cat > goals_only.v <<EOF
  > Theorem g : True.
  > Proof.
  >   exact I.
  > Qed.
  > EOF

  $ rocq-ed init goals_only.v
  $ rocq-ed goto --print-goals --position-line-column 2:1 goals_only.v
  Goal 1:
    ============================
    True
  
  $ rocq-ed stop goals_only.v
