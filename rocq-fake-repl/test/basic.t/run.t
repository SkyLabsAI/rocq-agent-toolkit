  $ dune build
  $ dune rocq top --toplevel rocq-fake-repl theories/file.v | sed 's/\/.*\/\(_build\/\)/$TESTCASE_ROOT\/\1/'
  -w
  -deprecated-native-compiler-option
  -w
  -native-compiler-disabled
  -native-compiler
  ondemand
  -boot
  -R
  $TESTCASE_ROOT/_build/install/default/lib/coq/theories
  Corelib
  -R
  $TESTCASE_ROOT/_build/default/theories
  test.theory
