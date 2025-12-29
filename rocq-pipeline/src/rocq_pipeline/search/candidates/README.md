# Candidates Module (Layer 3)

This module provides domain-agnostic abstractions for generating and correcting candidate actions during search.

## Purpose

The candidates layer bridges:
- **Layer 0/1**: Generic search algorithms (Strategy, Action, BeamSearch)
- **Layer 2**: Domain-specific execution (RocqTacticAction, LeanTacticAction)
- **Application**: LLM-based or heuristic generators (live in backend repos)

## Core Abstractions

### `Candidate`

A proposed action before execution. Domain-agnostic.

```python
@dataclass(frozen=True)
class Candidate:
    text: str        # "auto.", "e2e4", "rotate_90"
    logprob: float   # Confidence from generator
```

### `CandidateGenerator`

Generates candidates from state descriptions.

```python
class CandidateGenerator(Protocol):
    def generate(self, state_desc: str, *, limit: int | None = None) -> Iterator[Candidate]:
        """Yield candidates in descending probability order."""
```

### `CandidateRectifier`

Corrects failed candidates based on error feedback.

```python
class CandidateRectifier(Protocol):
    def rectify(self, state_desc: str, candidate: str, error: str) -> str | None:
        """Return fixed candidate, or None if unfixable."""
```

### `GeneratorStrategy`

Bridges generators to the Strategy interface.

```python
strategy = GeneratorStrategy(
    generator=my_llm_generator,         # CandidateGenerator
    get_state_desc=lambda c: c.goal(),  # Extract description
    to_action=RocqTacticAction,         # Simple conversion
    to_action_with_retry=RocqRetryAction,  # With rectification
    rectifier=my_rectifier,
    max_retries=3,
)
```

## Usage Pattern

### In rocq-agent-toolkit (Layer 3)

Define protocols, no implementations:

```python
from rocq_pipeline.search.candidates import (
    Candidate,
    CandidateGenerator,
    GeneratorStrategy,
)
```

### In backend (Application)

Implement generators and rectifiers:

```python
# brick_agents/proof/llm_generator.py

class LLMTacticGenerator(CandidateGenerator):
    def __init__(self, client: LLMClient, prompt_template: str):
        self._client = client
        self._template = prompt_template
    
    def generate(self, state_desc: str, *, limit: int | None = None):
        prompt = self._template.format(goal=state_desc)
        self._client.forward([{"role": "user", "content": prompt}])
        
        tactics = self._parse_response(self._client.content or "")
        for i, tactic in enumerate(tactics[:limit]):
            yield Candidate(text=tactic, logprob=-0.1 * i)
```

### Wiring it Together

```python
from rocq_pipeline.search.candidates import GeneratorStrategy
from rocq_pipeline.search.rocq.actions import RocqTacticAction, RocqRetryAction

strategy = GeneratorStrategy(
    generator=LLMTacticGenerator(llm_client, PROMPT),
    get_state_desc=lambda cursor: cursor.current_goal(),
    to_action=RocqTacticAction,
    to_action_with_retry=lambda t, r, n: RocqRetryAction(t, r, n),
    rectifier=LLMTacticRectifier(llm_client),
    max_retries=3,
)

# Use in search
search = BeamSearch(strategy=strategy, ...)
```

## Why This Design?

1. **Dependency inversion**: rocq-agent-toolkit defines protocols, backend implements them
2. **Domain-agnostic**: Same `CandidateGenerator` can work for Rocq, Lean, games, puzzles
3. **Composable**: Mix LLM generators with heuristic generators via `CompositeStrategy`
4. **Testable**: Mock generators for testing without LLM calls

## See Also

- `search/strategy.py` - Strategy base class
- `search/rocq/actions.py` - RocqRetryAction for rectification
- Backend examples: `brick_agents/proof/strategy/`

