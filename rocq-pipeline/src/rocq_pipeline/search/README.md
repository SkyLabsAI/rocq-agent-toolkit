# Search

The search module provides generic search infrastructure for agents working on MDPs.
It is especially focused on MDPs with **infinite action spaces**.

The module contains the following concepts:

* [Strategies](strategy.py) capture classes of related actions.
  For example, a strategy could encapsulate asking an LLM to generate several loop invariants in ranked order by likelihood. Each of these candidate invariants would become one element in the result of `rollout`.

* [Actions](action.py) capture searches for individual actions that can be taken in the MDP.
  `Action`s are allowed to fail and are also allowed to take multiple steps within the underlying MDP. This can be particulary important within the context of theorem proving because it allows an `Action` to refine the actual tactic combination that is run, e.g. if the original proposal does not type check, then an iteration can try to fix the typing errors.

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
