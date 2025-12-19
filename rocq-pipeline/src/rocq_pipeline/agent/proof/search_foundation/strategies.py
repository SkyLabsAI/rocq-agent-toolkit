from typing import Generator, Tuple, TypeVar, Optional
from .protocols import Strategy, LLMClient, StateT, Action
from .types import BeamNode
from .actions import SelfCorrectingAction

T = TypeVar("T", bound=StateT)

class LLMGenerationStrategy(Strategy[T]):
    """
    Standard LLM Strategy: 
    1. Formats prompt from state.
    2. Calls LLM.
    3. Wraps results in SelfCorrectingActions.
    """
    def __init__(
        self, 
        llm: LLMClient, 
        prompt_template: str,
        action_retries: int = 0
    ):
        self.llm = llm
        self.template = prompt_template
        self.retries = action_retries

    def rollout(self, node: BeamNode, state: T, n: int) -> Generator[Tuple[float, Action[T]], None, None]:
        # 1. Prepare Context (Generic)
        context_vars = state.format_prompt_context()
        try:
            prompt = self.template.format(**context_vars)
        except KeyError as e:
            # Fallback if template expects keys the state didn't provide
            prompt = f"Error formatting prompt: missing {e}. Context: {str(context_vars)}"

        # 2. Call LLM
        # Candidates is list of (text, logprob, finish_reason)
        candidates = self.llm.generate(prompt, n=n)

        # 3. Yield Actions
        for text, logprob, _ in candidates:
            # Create a smart action that owns its retry loop
            action = SelfCorrectingAction(
                initial_tactic=text.strip(),
                llm=self.llm,
                context_prompt=prompt,
                max_retries=self.retries
            )
            yield logprob, action