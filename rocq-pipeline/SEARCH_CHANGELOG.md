# Search Changes: Dedup, Repetition, Adapters

## Summary (Technical, Brief)

- Added per-action stable keys (`Action.key()` + `RocqTacticAction.key()`) for local dedup and repetition checks.
- Added repetition detection with explicit policy injection (`RepetitionPolicy`).
- Added state dedup via caller-supplied `state_key` to define domain-specific equivalence.
- Added domain-agnostic state lifecycle hooks in `search(...)`: `clone_state`, `apply_action`, `dispose_state`.
- Kept node history minimal: only action key per node + a per-node set of already-tried action keys.

## Decisions + Rationale

- Action key interface
  - Decision: `Action.key()` is concrete with a safe fallback; `RocqTacticAction` overrides with the tactic string.
  - Rationale: avoids forcing all actions to expose semantics while still enabling exact dedup where possible.

- Repetition policy injection
  - Decision: require explicit thresholds in `RepetitionPolicy` and only enforce repetition when provided.
  - Rationale: user control over thresholds and no hidden defaults.

- State dedup via `state_key`
  - Decision: make state equivalence caller-defined and optional.
  - Rationale: search core remains domain-agnostic and avoids binding to any proof-state representation.

- Lifecycle hooks (`clone_state`, `apply_action`, `dispose_state`)
  - Decision: inject state operations rather than assuming `.clone()` / `.dispose()`.
  - Rationale: supports backends without those methods (e.g., session-based systems) while preserving resource hygiene.

- Minimal action history
  - Decision: store only the action key per node and a local set of already-seen action keys.
  - Rationale: avoids passing full tactic histories while still enabling repetition pruning.

## Adapter Shapes

### Rocq (cursor-based)

```python
clone_state = lambda cursor: cursor.clone()
apply_action = lambda cursor, action: action.step(cursor)
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
        raise Action.FailedAction()
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
        raise Action.FailedAction()
    return state


def dispose_state(state):
    state.close()
```
