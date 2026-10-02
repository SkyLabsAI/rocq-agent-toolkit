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
  > Definition d := 3.
  > Definition e := 4.
  > EOF

  $ eval $(rocq-ed init print.v)
  $ rocq-ed goto --print-context=1 --position-line-column 2:1
     1| Definition a := 0.
     2| <CURSOR>Definition b := 1.
     3| Definition c := 2.

Printing after a command is part of the command's single server request.

  $ grep -c 'Request .* received' "$HOME/.cache/rocq-ed/$ROCQED_SESSION_ID/log"
  1

The whole document can be requested too.

  $ rocq-ed goto --print-context=all --position-line-column 2:1
     1| Definition a := 0.
     2| <CURSOR>Definition b := 1.
     3| Definition c := 2.
     4| Definition d := 3.
     5| Definition e := 4.
  $ rocq-ed goto --position-line-column 1:1
  $ rocq-ed steps --count-items=2
  $ rocq-ed backwards --count-items=1
  $ rocq-ed insert --text $'\nDefinition inserted := 42.'
  $ rocq-ed delete --count-items=1
  $ rocq-ed stop

--print-goals can be requested without printing context.

  $ cat > goals_only.v <<EOF
  > Theorem g : True.
  > Proof.
  >   exact I.
  > Qed.
  > EOF

  $ eval $(rocq-ed init goals_only.v)
  $ rocq-ed goto --print-goals --position-line-column 2:1
  Goal 1:
    ============================
    True
  $ grep -c 'Request .* received' "$HOME/.cache/rocq-ed/$ROCQED_SESSION_ID/log"
  1

The status command can print context and goals together, or goals alone.

  $ rocq-ed status --context-lines=1 --goals
     1| Theorem g : True.
     2| <CURSOR>Proof.
     3|   exact I.
  
  Goal 1:
    ============================
    True
  $ rocq-ed status --context-lines=none --goals
  Goal 1:
    ============================
    True
  $ rocq-ed status --context-lines=none
  $ rocq-ed status --json --goals
  rocq-ed: '--goals' and '--json' cannot be used together
  [124]
  $ rocq-ed status --json --context-lines=none
  rocq-ed: '--context-lines' and '--json' cannot be used together
  [124]
  $ rocq-ed stop
