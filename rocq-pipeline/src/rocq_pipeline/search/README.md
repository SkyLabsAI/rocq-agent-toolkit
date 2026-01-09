# Search

The search module provides generic search infrastructure for agents working on MDPs.
It is especially focused on MDPs with **infinite action spaces**.

The module contains the following concepts:

## Strategy and Action Abstractions

**Strategy** and **Action** provide a composable framework for agentic systems working with infinite action spaces, particularly suited for tool-calling agents and LLM-based systems.

```mermaid
graph LR
    S[Strategy] -->|rollout state| R[Rollout Generator]
    R -->|yields| PA["(probability, Action)"]
    PA -->|agent tries| A[Action.interact]
    A -->|succeeds| NS[New State]
    A -->|fails| R
    NS -->|continue| S
```

### Strategy

A **Strategy** proposes ranked action candidates. The [`rollout()`](strategy.py#L34-L52) method lazily generates `(probability, Action)` pairs in **decreasing probability order**, enabling efficient exploration of large or infinite action spaces.

**Key properties:**
- **Lazy generation**: Uses generators to avoid materializing entire action spaces
- **Ranked proposals**: Actions returned in decreasing probability (highest confidence first)
- **Composable**: Strategies can be combined via [`CompositeStrategy`](strategy.py#L94-L132), [`StagedStrategy`](strategy.py#L135-L204), etc.

**Example implementations:**
- [`SafeTacticStrategy`](../rocq/strategies.py#L13-L33): Wraps a single tactic as a strategy
- [`FirstTacticStrategy`](../rocq/strategies.py#L63-L85): Tries multiple tactics in ranked order
- [`OracleStrategy`](../../agent/proof/oracle_agent.py#L40-L58): Proposes actions by looking ahead in the document (useful for data extraction, but not synthesis of new proofs)

### Action

An **Action** represents a single executable operation. The [`interact(state)`](action.py#L30-L36) method transforms state and either returns a new state or raises [`Action.Failed`](action.py#L22-L28) if execution cannot proceed.

**Key properties:**
- **Explicit failure**: Uses exceptions rather than silent failures
- **State transformation**: `interact(state) → new_state`
- **Deduplication**: [`key()`](action.py#L38-L40) provides stable identifiers for repetition checks

**Example implementations:**
- [`RocqTacticAction`](../rocq/actions.py#L14-L47): Executes a single Rocq tactic
- [`RocqRetryAction`](../rocq/actions.py#L50-L158): Adds LLM-based rectification on failure

### Relationship

```mermaid
sequenceDiagram
    participant Agent
    participant Strategy
    participant Action
    participant State

    Agent->>Strategy: rollout(state)
    Strategy-->>Agent: (prob₁, action₁), (prob₂, action₂), ...
    loop Until success or exhausted
        Agent->>Action: interact(state)
        alt Success
            Action-->>Agent: new_state
            Agent->>Agent: break (continue with new_state)
        else Failure
            Action-->>Agent: Action.Failed
            Agent->>Agent: try next action
        end
    end
```

**Usage pattern** (see [`StrategyAgent.prove()`](../../agent/proof/strategy_agent.py#L95-L122)):
1. Strategy generates ranked actions via `rollout()`
2. Agent iterates through actions in probability order
3. Each action is executed via `interact(state)`
4. On success, agent continues with new state; on failure, tries next action
5. Process repeats until goal reached or all actions exhausted

## Search Dynamics
The [search/](search/) directory contains a [generic search algorithm](search/search.py) that is parametric over the state type which allows it to be used in many contexts.

The search algorithm is parameterized by a [Frontier](search/frontier.py) which allows configuring the search strategy to act with different exploration policies, e.g. BFS, DFS, A*, or Beam searches and also configure other knobs such as sampling rather than deterministic exploration, de-duplication of states, early termination, etc.

### Components

- **`search.py`** - Core search loop with interleaved rollouts
  - `search()` - Generic search function with depth limiting and state deduplication
  - `continue_search()` - Generic search function with depth limiting and state deduplication
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

- **`beam.py`** - Beam search using frontier composition
  - `BeamSearch[T]` - Configurable beam search (PQueue → SingleDepth → SavingSolutions)
  - Supports heuristic guidance, depth limiting, state deduplication


## The Rocq Instantiation
The [rocq/](rocq/) directory contains several building blocks that might be useful for connecting these to Rocq.
