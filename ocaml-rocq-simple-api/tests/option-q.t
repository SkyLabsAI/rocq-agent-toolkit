  $ cat > commands.txt <<EOF
  > run 0 "Locate nat."
  > EOF

  $ cat commands.txt | rocq-simple-api.toplevel -q
  Error: input_value: bad object.
  [1]
