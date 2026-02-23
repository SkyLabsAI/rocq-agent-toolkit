#!/usr/bin/env bash

echo "Updating run-release.t.disabled from run.t..."

exec > run-release.t.disabled

cat <<'EOF'
Basic test for `auto-prover`.
Here, unlike `run.t`, we assume that both Python and Rocq dependencies are
already installed.
This test is disabled by default, but CI for releases will enable it.

The tests are otherwise the same, and `./regen-run-release.sh` can be used to
keep them in sync.

Copy dune project from source tree to separate folder:

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .

Run installed `auto-prover`:

  $ auto-prover foo.v
EOF

# Sync the test "meat" from `run.t`, that is, the lines after the `auto-prover`
# invocation.
awk '/auto-prover foo.v/ { do_print = 1; next; } do_print == 1 { print $0; }' < run.t
