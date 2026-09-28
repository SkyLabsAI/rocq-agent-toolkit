export DUNE_CACHE=disabled
unset DUNE_ACTION_TRACE_DIR
export LC_ALL=C
export TERM=dumb

mkdir user
mkdir test-dir

unset XDG_CACHE_HOME
export HOME=$PWD/user
cd test-dir
