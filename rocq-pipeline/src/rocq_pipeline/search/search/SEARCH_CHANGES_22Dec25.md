# Search Changes In This Commit - 22 Dec 2025

**Note:** This file is a **temporary placeholder** for Usama, Saad and Gregory to communicate on the latest changes in this code. It should be removed once all the code in all the branches is consolidated. 

## Summary

- Added a generic search engine with explicit frontier abstractions.
- Updated the core `Action`/`Strategy` APIs to support the search engine's
  deduplication, repetition checks, and state lifecycle hooks.

## New Modules

- `rocq_pipeline/search/search/search.py`
  - `search(...)` function that expands a frontier by interleaving rollouts.
  - `RepetitionPolicy` for local action-loop pruning.
  - `Node` with cached rollouts and minimal action history.
  - `Interleaver` + `interleave_continue(...)` for fair rollout interleaving.
- `rocq_pipeline/search/search/frontier.py`
  - `Frontier` interface and concrete implementations:
    `DFS`, `BFS`, `PQueue`, `SingleDepth`, `Sampled`.

## Updated APIs

- `rocq_pipeline/search/action.py`
  - Added `Action.key()` for stable action identifiers used by dedup/repetition
    logic in `search(...)`.
- `rocq_pipeline/search/rocq/actions.py`
  - `TacticAction.key()` now returns the tactic string for stable dedup.
- `rocq_pipeline/search/strategy.py`
  - `Strategy.Rollout` is now a `Generator[(float, Action)]` type alias.
  - `Strategy.rollout(state, max_rollout=None, context=None)` accepts optional
    context and returns an ordered rollout.
  - `CompositeStrategy` interleaves child rollouts fairly.

## Search Behavior And Hooks

- `search(...)` accepts optional hooks:
  - `clone_state(state)`, `apply_action(state, action)`, `dispose_state(state)`.
  - Defaults are duck-typed: `state.clone()`, `action.interact(...)`,
    `state.dispose()`.
- Optional state deduplication via `state_key(state)` and repetition pruning
  via `RepetitionPolicy`.

## Adapter Shapes

### Rocq (cursor-based)

```python
clone_state = lambda cursor: cursor.clone()
apply_action = lambda cursor, action: action.interact(cursor)
dispose_state = lambda cursor: cursor.dispose()

search(
    strategy=rocq_strategy,
    start=rocq_cursor,
    frontier=frontier_type,
    repetition_policy=policy,
    state_key=rocq_state_key,
    clone_state=clone_state,
    apply_action=apply_action,
    dispose_state=dispose_state,
)
```

### Lean (single session + checkpoints)

```python
# state = (session, checkpoint_id)

def clone_state(state):
    return state


def apply_action(state, action):
    session, checkpoint = state
    session.restore(checkpoint)
    ok, next_checkpoint = session.run(action.tactic)
    if not ok:
        raise Action.Failed()
    return (session, next_checkpoint)


def dispose_state(state):
    pass
```

### Lean (forked sessions)

```python
# state = session

def clone_state(state):
    return state.fork()


def apply_action(state, action):
    ok = state.run(action.tactic)
    if not ok:
        raise Action.Failed()
    return state


def dispose_state(state):
    state.close()
```

## Usage Sketch

```python
from rocq_pipeline.search.search.search import search, RepetitionPolicy
from rocq_pipeline.search.search.frontier import BFS

result_frontier = search(
    strategy=my_strategy,
    start=initial_state,
    frontier=BFS,
    beam_width=4,
    explore_width=2,
    repetition_policy=RepetitionPolicy(3, 2, 4, 2),
    state_key=lambda s: s.hash_key(),
)
```
