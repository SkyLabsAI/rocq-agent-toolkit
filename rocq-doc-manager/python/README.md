Python API for the Rocq Document Manager
========================================

This library can be used to run Rocq document managers from Python.

## Build Invariant

Always make sure that the contents of `skylabs-fm` is installed: `workspace$ dune build @fmdeps/skylabs-fm/install`.
Also, make sure to build the dependencies of the file you want to load: `<my_proj>$ dune build`.

Additionally, make sure that no ongoing dune build is happening; the python code currently works around a `dune exec` bug by ignoring the global build lock from dune.

## Example

The following example shows an example use case for `RocqDocManager`:

```python
# Process "foo.v"; use [dune exec] to run the document manager
#
# Note: context manager automatically quits the rocq-doc-manager at scope close
with RocqDocManager("foo.v", dune=True) as rdm:
    assert isinstance(rdm.load_file(), RocqDocManager.Resp)
    
    data = rdm.run_command("go.")
    if isinstance(data, RocqDocManager.Resp):
        next_goal = data.result["open_subgoals"]
        ...
    else:
        ...
```
