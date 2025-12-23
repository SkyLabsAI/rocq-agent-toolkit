# Search Architecture

> **Note:** This search module is designed to be domain-agnostic and will be moved to a separate package in the future.

## Overview

The search module uses a 3-layer architecture separating generic algorithms from domain-specific code:

```
Layer 3: Application (LLM tactic generators, scorers, proof goals)
         ↓
Layer 2: Domain Adapters (search/rocq/, search/lean/)
         ↓
Layer 1: Generic Algorithms (search/search/)
         ↓
Layer 0: Core Abstractions (Action[T], Strategy[T])
```

## Layer 0: Core Abstractions

**Location:** `search/` (root level)

- **`Action[T]`** - Interface for state transformations
  - `interact(state: T) -> T` - Apply action
  - `key() -> str` - Unique identifier for deduplication
  - `Action.Failed` - Exception for failed actions

- **`Strategy[T]`** - Interface for action generation
  - `rollout(state, max_rollout, context) -> Rollout[T]` - Generate `(probability, Action)` pairs
  - `CompositeStrategy[T]`, `GuardStrategy[T]` - Strategy combinators

## Layer 1: Generic Search Algorithms

**Location:** `search/search/`

All algorithms are generic over state type `T` with no domain dependencies.

### Components

- **`search.py`** - Core search loop with interleaved rollouts
  - `search()` - Generic search function with depth limiting and state deduplication
  - `Node[T]` - Search tree node with action history
  - `RepetitionPolicy` - Action repetition detection

- **`beam.py`** - Beam search using frontier composition
  - `BeamSearch[T]` - Configurable beam search (PQueue → SingleDepth → SavingSolutions)
  - Supports heuristic guidance, depth limiting, state deduplication
  - `StateManip[T]` - Helper for imperative state management

- **`guidance.py`** - Heuristic state scoring
  - `Guidance[T]` - Abstract scoring interface (lower scores = better states)
  - `UniformGuidance[T]` - Default uniform scoring

- **`frontier.py`** - Collection management for search states
  - `Frontier[T, Node]` - Abstract frontier interface
  - `DFS[T]`, `BFS[T]`, `PQueue[T]` - Standard frontiers
  - `SingleDepth[T, Node]` - Beam-style single-depth expansion
  - `SavingSolutions[T, Node]` - Solution tracking
  - `Deduplicate[T, Node]`, `Sampled[T, Node]` - Frontier wrappers

### Key Features

- **Depth Limiting**: `max_depth` parameter in `search()` prevents infinite exploration
- **State Deduplication**: Optional `state_key` parameter prevents revisiting states
- **Composable Frontiers**: Stack frontier wrappers to customize search behavior
- **Resource Management**: Explicit clone/dispose hooks for imperative states

## Layer 2: Domain Adaptations

**Location:** `search/rocq/`, `search/lean/`, etc.

Domain-specific implementations of `Action[T]` and `Strategy[T]`:

- **`search/rocq/actions.py`** - `TacticAction(Action[RocqCursor])` for Coq tactics
- **`search/rocq/strategies.py`** - Domain-specific tactic generation

Layer 2 modules can import Layer 0 abstractions and domain libraries (e.g., `rocq_doc_manager`), but not Layer 1 algorithms.

## Layer 3: Application Integration

**Location:** Outside `search/` (agent modules, application code)

Integrates search with:
- Tactic generators (LLM-based or mechanical)
- State scorers/guidance (LLM-based or heuristic)
- Domain-specific goal representation

### Example Usage

```python
from rocq_pipeline.search import Strategy
from rocq_pipeline.search.search.beam import BeamSearch
from rocq_pipeline.search.search.guidance import Guidance
from rocq_pipeline.search.rocq.actions import TacticAction

# Define guidance (Layer 3)
class ProofGuidance(Guidance[RocqCursor]):
    def score(self, state: RocqCursor, logprob: float | None = None) -> float:
        return compute_proof_score(state)  # LLM or heuristic

# Define strategy (Layer 3)
class LLMTacticStrategy(Strategy[RocqCursor]):
    def rollout(self, state, max_rollout=None, context=None):
        tactics = llm_generate_tactics(state)
        for prob, tactic_str in tactics:
            yield (prob, TacticAction(tactic_str))  # Layer 2 action

# Run beam search (Layer 1)
search = BeamSearch(
    strategy=LLMTacticStrategy(),
    guidance=ProofGuidance(),
    is_solved=lambda s: s.current_goal().is_qed(),
    beam_width=5,
    explore_width=10,
    max_depth=50,
    stop_on_first_solution=True,
    state_key=lambda s: s.serialize(),  # Deduplicate proof states
)
solutions = search.search(initial_cursor)
```

## Testing

Layer 1 algorithms can be tested with simple domains (grids, puzzles) without requiring domain-specific infrastructure. See `tests/rocq_pipeline/search/test_grid_beam.py` for examples.
