# Action Beam Search Architecture

This document outlines the proposed architectural design for the Action Beam Search code. The design is intended to ensure strict separation between the search algorithm, the prompt engineering/LLM logic, and the specific theorem prover (Rocq).

This separation allows the core search logic to be reused for other domains (e.g., Lean 4) or for non-LLM baselines (e.g., generic search) without code duplication.

## 1. High-Level Overview

The system is divided into three distinct layers of abstraction:

1. **Layer 1: Search Foundation (Core)**
* **Responsibility:** Generic search logic, plus generic LLM-driven expansion/retry utilities.
* **Dependencies:** Pure Python (no Rocq/Lean-specific dependencies).
* **Key Concept:** Operates on generic types `T` (State) and protocols (Interfaces).


2. **Layer 2: Domain Middleware (Adapters)**
* **Responsibility:** Binding the Core to a specific domain (Rocq).
* **Dependencies:** `search_foundation` + `rocq_doc_manager`.
* **Key Concept:** Maps `RocqCursor` to `StateT`. Defines `Action` implementations.


3. **Layer 3: Application Layer (Agent)**
* **Responsibility:** Configuration, Prompts, and Execution.
* **Dependencies:** `rocq_pipeline` + Layer 2.
* **Key Concept:** Combines the LLM Generation and Beam Search (Search Engine).



---

## 2. Layer Details

### Layer 1: Search Foundation

**Location:** `src/rocq_pipeline/agent/proof/search_foundation/`

This module defines the "Shape" of the search. It does not know what a "proof" is; it only knows about **States**, **Actions**, and **Scores**.

* **`beam_search.py`**: The generic engine. It manages the queue, threads, and budget. It calls `strategy.rollout(node, state, n)` to get candidates.
  * Parallelism: `parallel_beams > 1` is intended for concurrent candidate generation/expansion; domain adapters should verify tactics on cloned cursors/states.
* **`protocols.py`**: The contract definitions.
* `StateT`: Must implement:
  * `get_goals() -> list[str]`
  * `apply_tactic(str) -> (success, new_goals, next_state, error_msg)`
  * `format_prompt_context() -> dict`
* `Strategy[T]`: Must implement `rollout(node, state, n) -> Generator[(logprob, Action[T])]`.
* `LLMClient`: Abstract interface for text generation (`generate(prompt, n)`).


* **`strategies.py`**: Generic logic for LLM-based expansion. Knows *how* to call an API and parse results, but not *what* to ask.
* **`actions.py`**: Contains `SelfCorrectingAction`. This implements the generic "Try → Fail → Fix" loop using the `StateT` protocol.

### Layer 2: Rocq Adapter (Middleware)

**Location:** `src/rocq_pipeline/agent/proof/beam/`

This module bridges the gap between the Generic Foundation and the Rocq Toolkit.

* **`beam.py` (The Adapter)**:
* Defines `RocqStateAdapter`: Wraps `RocqCursor`. Implements `StateT`.
* Translates generic `apply_tactic` calls into `cursor.run_command()` on a cloned cursor.
* Uses `ProofState` to extract goal strings from `current_goal()`.


* **`guidance.py`**:
* Implements generic `GuidanceProtocol` to score Rocq states.



### Layer 3: The Application

**Location:** `src/rocq_pipeline/agent/`

This is where the user's intent is defined.

* **`prompts.py`**: Contains the specific prompts (e.g., `ROCQ_TACTIC_PROMPT`).
* **`beam_search_agent.py`**: The composition root.
1. Instantiates the **Adapter** (`RocqStateAdapter`).
2. Instantiates the **Strategy** (`LLMGenerationStrategy`) with the specific **Prompt**.
3. Runs the **Search Foundation**.
4. TODO: Wire `beam_search_agent.py` to the new `search_foundation` modules.



---

## 3. Extensibility Guide

### How to use this for Non-LLM Experiments?

To run a baseline (e.g., "Try `tac1` then `tac2`"):

1. Create a class `FixedListStrategy` that implements `Strategy[T]`.
2. Have it yield `SimpleAction` objects (no retry loop).
3. Pass this strategy to `ActionBeamSearch`.
*No LLM code is touched.*

### How to use this for Lean 4?

1. **Import Core:** Import `search_foundation`.
2. **Create Adapter:** Create `LeanStateAdapter` wrapping `LeanState`.
3. **Define Strategy:** Instantiate `LLMGenerationStrategy` with a Lean-specific prompt template.
4. **Run:** `ActionBeamSearch(strategy=lean_strategy, initial_state=lean_adapter)`.

---

## 4. Directory Structure Proposal

```text
src/rocq_pipeline/agent/proof/
├── search_foundation/          <-- [LAYER 1] Generic Core
│   ├── __init__.py
│   ├── beam_search.py          # The Algorithm
│   ├── types.py                # Data Classes (BeamNode, SearchResult)
│   ├── protocols.py            # Interfaces (StateT, Action, Strategy)
│   ├── strategies.py           # Generic LLM Logic
│   └── actions.py              # Generic Retry/Fix Logic
│
├── beam/                       <-- [LAYER 2] Rocq Adapters
│   ├── __init__.py
│   ├── beam.py                 # RocqStateAdapter & RocqActionBeamSearch
│   └── guidance.py             # Rocq-specific Heuristics
│
└── ...                         <-- [LAYER 3] App (Agent implementation)

```
