# Search Module Guide

A practical guide to understanding the proof search infrastructure.

## Core Concepts

### What Each Component Does

| Component | Question It Answers | Example |
|-----------|---------------------|---------|
| **Strategy** | "What actions should I try from this state?" | LLM suggests `["auto.", "simpl.", "reflexivity."]` |
| **Action** | "How do I execute this action?" | Run `cursor.insert_command("auto.")` |
| **Frontier** | "Which pending states should I explore next?" | Priority queue ordered by score |
| **Guidance** | "How promising is this state?" | Fewer remaining goals = better |
| **Node** | "What's the history of this search path?" | Tracks parent chain, depth, action keys |
| **StateManipulator** | "How do I clone/dispose states?" | `cursor.clone()`, `cursor.dispose()` |

### How They Connect

```
┌─────────────────────────────────────────────────────────────────────┐
│                         SEARCH LOOP                                  │
│                                                                      │
│   ┌──────────┐     "what should I try?"    ┌──────────┐             │
│   │  STATE   │ ─────────────────────────▶  │ STRATEGY │             │
│   └──────────┘                             └──────────┘             │
│        │                                        │                   │
│        │                           Iterator[(prob, Action)]         │
│        │                                        │                   │
│        │     ┌──────────┐                       │                   │
│        └────▶│  ACTION  │◀──────────────────────┘                   │
│              └──────────┘                                           │
│                   │                                                 │
│            interact(state) → new_state (or raise Failed)            │
│                   │                                                 │
│                   ▼                                                 │
│   ┌──────────────────────────────────────────────────────────────┐  │
│   │                         FRONTIER                              │  │
│   │   push(new_state)  ──▶  [state pool]  ──▶  take(n)           │  │
│   └──────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

## Frontier Types

The frontier determines the **search algorithm**:

| Search Type | Frontier | Behavior |
|-------------|----------|----------|
| **DFS** | `DFS()` | Explore deepest node first |
| **BFS** | `BFS()` | Explore all depth-N before depth-N+1 |
| **Best-First** | `PQueue(scorer, cmp)` | Always explore highest-scoring node |
| **Beam Search** | `SingleDepth(PQueue(...))` | Best-K nodes at each depth level |

Frontiers compose via wrapping:

```python
base = PQueue(scorer, comparator)      # Priority ordering
beam = SingleDepth(base)               # Beam behavior (clear on depth increase)
dedup = DeduplicateWithKey(beam, ...)  # Skip visited states
final = SavingSolutions(dedup, ...)    # Track solutions
```

## Beam Search Dry Run

Configuration: `beam_width=2`, `explore_width=3`

### Initial State

```
Node A (depth=0, score=1.0)
  state: cursor at goal "∀ n, n + 0 = n"
```

### Iteration 1

**`take(2)`** pulls Node A from frontier:

```
Frontier before: [A(d=0, s=1.0)]
Frontier after:  []  ← empty
```

**Strategy generates tactics** for Node A:

```
"induction n." → would create 2 subgoals
"intro n."     → would create 1 subgoal
"reflexivity." → would fail
```

**Apply tactics:**

1. `"induction n."` succeeds → creates **Node B** (depth=1, 2 goals, score=2.001)

   ```
   SingleDepth.push(NodeB):
     depth (1) > max_depth (0)?  → YES
     *** CLEAR frontier ***
     max_depth = 1
     PQueue.push(NodeB)
   ```

2. `"intro n."` succeeds → creates **Node C** (depth=1, 1 goal, score=1.001)

   ```
   SingleDepth.push(NodeC):
     depth (1) > max_depth (1)?  → NO (same depth)
     *** NO CLEAR ***
     PQueue.push(NodeC)
   ```

3. `"reflexivity."` fails → nothing pushed

**Frontier after iteration 1:**

```
[C(d=1, s=1.001), B(d=1, s=2.001)]
 ↑ C is better (lower score)
```

### Iteration 2

**`take(2)`** pulls both C and B (C first, better score):

```
Candidates: [C, B]
Frontier: []
```

**Strategy generates tactics** for Node C (1 goal remaining):

```
"reflexivity." → would SOLVE IT (0 goals)
```

**Apply tactic:**

1. `"reflexivity."` on C succeeds → creates **Node D** (depth=2, solved!)

   ```
   SavingSolutions.push(NodeD):
     is_solution(NodeD)?  → YES!
     solutions.append(NodeD)
     stop = True  ← stop_on_first_solution
   ```

### Termination

**`take(2)`** returns `None` because `stop=True`:

```python
if not candidates:
    return worklist  # Search complete!
```

**Result:** `solutions = [NodeD]` 🎉

## Key Behaviors

### SingleDepth Clears on Depth Increase

When a node at depth N+1 is pushed and `max_depth` is N:
- The entire frontier is **cleared**
- Only depth N+1 nodes survive
- This is the "beam" behavior—discard shallower nodes

### PQueue Orders by Score

- Lower score = higher priority (explored first)
- Ties broken by insertion order
- Guidance provides the scoring function

### SavingSolutions Tracks Winners

- Checks `is_solution()` on every push
- If `stop_on_first_solution=True`, stops search immediately
- Otherwise, collects all solutions found

## Layer Structure

```
rocq_pipeline/search/
├── action.py           # Layer 0: Action base class
├── strategy.py         # Layer 0: Strategy base class
│
├── search/             # Layer 1: Generic algorithms
│   ├── beam.py         # BeamSearch orchestrator
│   ├── frontier.py     # DFS, BFS, PQueue, SingleDepth, etc.
│   ├── guidance.py     # Guidance scoring interface
│   └── search.py       # Core search loop, Node, StateManipulator
│
├── rocq/               # Layer 2: Rocq domain
│   ├── actions.py      # RocqTacticAction
│   ├── manip.py        # RocqManipulator (clone/dispose)
│   └── strategies.py   # Rocq-specific strategies
│
└── candidates/         # Layer 3: Candidate generation (future)
    └── ...             # CandidateGenerator, GeneratorStrategy
```

**Dependency rule:** Higher layers import lower layers, never the reverse.

## Quick Reference

### Running a Search

```python
from rocq_pipeline.search.search.beam import BeamSearch
from rocq_pipeline.search.rocq.actions import RocqTacticAction
from rocq_pipeline.search.rocq.manip import RocqManipulator

search = BeamSearch(
    strategy=my_strategy,
    is_solved=lambda cursor: cursor.current_goal() is None,
    beam_width=5,
    explore_width=10,
    max_depth=50,
    stop_on_first_solution=True,
    freshen=RocqManipulator(),
)

solutions = search.search(initial_cursor)
```

### Creating a Simple Strategy

```python
from rocq_pipeline.search import Strategy
from rocq_pipeline.search.rocq.actions import RocqTacticAction

class MyStrategy(Strategy[RocqCursor]):
    def rollout(self, state, max_rollout=None, context=None):
        tactics = ["auto.", "simpl.", "reflexivity."]
        for i, tactic in enumerate(tactics[:max_rollout]):
            yield (1.0 - i * 0.1, RocqTacticAction(tactic))
```

### Composing Strategies

```python
from rocq_pipeline.search.strategy import CompositeStrategy

combined = CompositeStrategy([
    SafeTacticStrategy("verify_spec"),
    MyLLMStrategy(),
    FallbackStrategy(),
])
```

Composite interleaves rollouts from all children by probability.

## Extracting Search Results

### Successful Paths

Solutions are available via `SavingSolutions.solutions()`. Each solution is a `Node` with a `parent` pointer, allowing path reconstruction:

```python
def get_path(node: Node) -> list[str]:
    """Walk parent chain to get the action sequence."""
    actions = []
    while node is not None:
        if node._action_key:
            actions.append(node._action_key)
        node = node.parent
    return list(reversed(actions))

# Usage
result = search(...)
for solution in result.solutions():
    path = get_path(solution)
    print(path)  # ["intro n.", "reflexivity."]
```

### What's Tracked vs. Not Tracked

| Information | Available? | How |
|-------------|------------|-----|
| Successful solution states | ✅ | `result.solutions()` |
| Path to each solution | ✅ | Walk `Node.parent` chain |
| All visited nodes | ✅ | Use `RememberTrace` frontier wrapper |
| Failed action attempts | ❌ | Not tracked by default |

### Full Tree via Tracing

To capture the complete search tree including failures, use OpenTelemetry-style tracing in `search.py`:

```python
# In search.py process() function

with trace_context("search_action") as span:
    span.set_attribute("parent.id", id(candidate))
    span.set_attribute("parent.depth", candidate.depth)
    span.set_attribute("action.key", action_key)
    
    fresh_state = smanip.copy(candidate.state)
    try:
        next_state = action.interact(fresh_state)
        new_node = Node(next_state, candidate, action_key=action_key)
        worklist.push(new_node, parent)
        
        span.set_attribute("success", True)
        span.set_attribute("child.id", id(new_node))
        
    except Action.Failed as e:
        smanip.dispose(fresh_state)
        
        span.set_attribute("success", False)
        span.set_attribute("error", e.message or "")
```

This produces trace spans that can be collected by OpenTelemetry backends (Jaeger, Honeycomb, etc.) and reconstructed into a full tree:

```
beam_search
├── search_action {parent.id: 123, action.key: "induction n.", success: true, child.id: 456}
├── search_action {parent.id: 123, action.key: "reflexivity.", success: false, error: "Cannot apply"}
├── search_action {parent.id: 456, action.key: "auto.", success: true, child.id: 789}
└── ...
```

From these traces, rebuild the tree:

```python
def build_tree_from_traces(spans: list) -> dict:
    """Reconstruct search tree from trace spans."""
    tree = {}
    for span in spans:
        if span["name"] == "search_action":
            parent_id = span["attributes"]["parent.id"]
            if parent_id not in tree:
                tree[parent_id] = []
            tree[parent_id].append({
                "action": span["attributes"]["action.key"],
                "success": span["attributes"]["success"],
                "error": span["attributes"].get("error"),
                "child_id": span["attributes"].get("child.id"),
            })
    return tree
```

