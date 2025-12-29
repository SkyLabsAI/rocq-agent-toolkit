"""Tests for candidate generation infrastructure."""

from collections.abc import Iterator

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.candidates import (
    Candidate,
    CandidateGenerator,
    CandidateRectifier,
    GeneratorStrategy,
)

# Test fixtures


class DummyState:
    def __init__(self, desc: str, solved: bool = False):
        self.desc = desc
        self.solved = solved


class DummyAction(Action[DummyState]):
    def __init__(self, text: str, should_fail: bool = False):
        self._text = text
        self._should_fail = should_fail

    def interact(self, state: DummyState) -> DummyState:
        if self._should_fail:
            raise Action.Failed(f"Action '{self._text}' failed")
        return DummyState(f"{state.desc} + {self._text}", self._text == "solve")

    def key(self) -> str:
        return self._text


class SimpleGenerator(CandidateGenerator):
    """Generator that returns fixed candidates."""

    def __init__(self, candidates: list[tuple[str, float]]):
        self._candidates = candidates

    def generate(
        self, state_desc: str, *, limit: int | None = None
    ) -> Iterator[Candidate]:
        items = self._candidates[:limit] if limit else self._candidates
        for text, logprob in items:
            yield Candidate(text=text, logprob=logprob)


class SimpleRectifier(CandidateRectifier):
    """Rectifier that fixes known errors."""

    def __init__(self, fixes: dict[tuple[str, str], str]):
        self._fixes = fixes  # (candidate, error) -> fixed

    def rectify(self, state_desc: str, candidate: str, error: str) -> str | None:
        return self._fixes.get((candidate, error))


# Tests


def test_candidate_creation():
    """Test Candidate dataclass."""
    c = Candidate(text="auto.", logprob=-0.5)
    assert c.text == "auto."
    assert c.logprob == -0.5


def test_simple_generator():
    """Test a simple candidate generator."""
    gen = SimpleGenerator(
        [
            ("action1", -0.1),
            ("action2", -0.2),
            ("action3", -0.3),
        ]
    )

    candidates = list(gen.generate("some state"))
    assert len(candidates) == 3
    assert candidates[0].text == "action1"
    assert candidates[0].logprob == -0.1


def test_generator_with_limit():
    """Test generator respects limit parameter."""
    gen = SimpleGenerator(
        [
            ("action1", -0.1),
            ("action2", -0.2),
            ("action3", -0.3),
        ]
    )

    candidates = list(gen.generate("some state", limit=2))
    assert len(candidates) == 2
    assert candidates[1].text == "action2"


def test_generator_strategy_basic():
    """Test GeneratorStrategy with simple actions."""
    gen = SimpleGenerator(
        [
            ("step1", -0.1),
            ("step2", -0.2),
        ]
    )

    strategy = GeneratorStrategy(
        generator=gen,
        get_state_desc=lambda s: s.desc,
        to_action=lambda t: DummyAction(t),
    )

    state = DummyState("initial")
    rollout = list(strategy.rollout(state, max_rollout=10))

    assert len(rollout) == 2
    assert rollout[0][0] == -0.1  # logprob
    assert rollout[0][1].key() == "step1"
    assert rollout[1][0] == -0.2
    assert rollout[1][1].key() == "step2"


def test_generator_strategy_no_state_desc():
    """Test GeneratorStrategy when state has no description."""
    gen = SimpleGenerator([("action", -0.1)])

    strategy = GeneratorStrategy(
        generator=gen,
        get_state_desc=lambda s: None,  # No description
        to_action=lambda t: DummyAction(t),
    )

    state = DummyState("any")
    rollout = list(strategy.rollout(state))

    assert len(rollout) == 0  # No candidates generated


def test_generator_strategy_with_max_rollout():
    """Test GeneratorStrategy respects max_rollout."""
    gen = SimpleGenerator(
        [
            ("a1", -0.1),
            ("a2", -0.2),
            ("a3", -0.3),
            ("a4", -0.4),
        ]
    )

    strategy = GeneratorStrategy(
        generator=gen,
        get_state_desc=lambda s: s.desc,
        to_action=lambda t: DummyAction(t),
    )

    state = DummyState("test")
    rollout = list(strategy.rollout(state, max_rollout=2))

    assert len(rollout) == 2


def test_generator_strategy_with_retry():
    """Test GeneratorStrategy with retry-capable actions."""
    gen = SimpleGenerator([("action", -0.1)])
    rectifier = SimpleRectifier({})

    retry_action_called = False

    def to_action_with_retry(text, rect, retries):
        nonlocal retry_action_called
        retry_action_called = True
        assert text == "action"
        assert rect is rectifier
        assert retries == 3
        return DummyAction(text)

    strategy = GeneratorStrategy(
        generator=gen,
        get_state_desc=lambda s: s.desc,
        to_action=lambda t: DummyAction(t),
        to_action_with_retry=to_action_with_retry,
        rectifier=rectifier,
        max_retries=3,
    )

    state = DummyState("test")
    rollout = list(strategy.rollout(state))

    assert retry_action_called
    assert len(rollout) == 1


def test_generator_strategy_no_retry_when_disabled():
    """Test GeneratorStrategy uses simple action when retry disabled."""
    gen = SimpleGenerator([("action", -0.1)])

    simple_action_called = False

    def to_action(text):
        nonlocal simple_action_called
        simple_action_called = True
        return DummyAction(text)

    strategy = GeneratorStrategy(
        generator=gen,
        get_state_desc=lambda s: s.desc,
        to_action=to_action,
        to_action_with_retry=lambda t, r, n: DummyAction(t),
        rectifier=SimpleRectifier({}),
        max_retries=0,  # Disabled
    )

    state = DummyState("test")
    list(strategy.rollout(state))

    assert simple_action_called


def test_simple_rectifier():
    """Test SimpleRectifier fixes known errors."""
    rectifier = SimpleRectifier(
        {
            ("broken", "Error: syntax"): "fixed",
        }
    )

    result = rectifier.rectify("goal", "broken", "Error: syntax")
    assert result == "fixed"

    # Unknown error returns None
    result = rectifier.rectify("goal", "broken", "Unknown error")
    assert result is None
