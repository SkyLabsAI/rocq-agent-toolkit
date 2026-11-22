  $ ${DUNE:-dune} build
  $ ${DUNE:-dune} rocq top --toplevel rocq-fake-repl theories/file.v | sed -e 's/\/.*\/\(_build\/\)/$TESTCASE_ROOT\/\1/' -e 's|\.packages/[^/]*/lib|.packages/HASH/lib|'
  -w
  -deprecated-native-compiler-option
  -w
  -native-compiler-disabled
  -native-compiler
  ondemand
  -boot
  -I
  $TESTCASE_ROOT/_build/_private/default/.packages/HASH/lib
  -package
  rocq-core
  -R
  $TESTCASE_ROOT/_build/default/theories
  test.theory
