from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any

JsonPrimitive = str | int | float | bool | None
JsonValue = JsonPrimitive | list["JsonValue"] | dict[str, "JsonValue"]


def coerce_int(value: Any, default: int = 0) -> int:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return default
    return default


def coerce_float(value: Any, default: float = 0.0) -> float:
    if isinstance(value, bool):
        return float(int(value))
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return default
    return default


def to_json_value(value: Any) -> JsonValue:
    """Best-effort JSON conversion that preserves structure for basic types."""
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, list):
        return [to_json_value(v) for v in value]
    if isinstance(value, tuple):
        return [to_json_value(v) for v in value]
    if isinstance(value, dict):
        return {str(k): to_json_value(v) for k, v in value.items()}
    if hasattr(value, "model_dump"):
        try:
            return to_json_value(value.model_dump())
        except Exception:
            return repr(value)
    return repr(value)


def to_json_object(value: Any) -> dict[str, JsonValue]:
    if not isinstance(value, dict):
        return {}
    return {str(k): to_json_value(v) for k, v in value.items()}


def to_json_object_list(value: Any) -> list[dict[str, JsonValue]]:
    if not isinstance(value, list):
        return []
    return [to_json_object(item) for item in value if isinstance(item, dict)]


@dataclass(slots=True)
class LLMRequest:
    messages: list[dict[str, JsonValue]] = field(default_factory=list)
    model: str | None = None
    stream: bool | None = None
    tool_choice: str | dict[str, JsonValue] | None = None
    tools: list[dict[str, JsonValue]] = field(default_factory=list)
    provider: dict[str, JsonValue] | None = None
    extra: dict[str, JsonValue] = field(default_factory=dict)

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> LLMRequest:
        tool_choice_raw = payload.get("tool_choice")
        tool_choice: str | dict[str, JsonValue] | None
        if isinstance(tool_choice_raw, str):
            tool_choice = tool_choice_raw
        elif isinstance(tool_choice_raw, dict):
            tool_choice = to_json_object(tool_choice_raw)
        else:
            tool_choice = None

        model = payload.get("model")
        stream = payload.get("stream")
        provider = payload.get("provider")
        known_keys = {"messages", "model", "stream", "tool_choice", "tools", "provider"}
        extra = {
            str(k): to_json_value(v)
            for k, v in payload.items()
            if str(k) not in known_keys
        }
        return cls(
            messages=to_json_object_list(payload.get("messages")),
            model=model if isinstance(model, str) else None,
            stream=stream if isinstance(stream, bool) else None,
            tool_choice=tool_choice,
            tools=to_json_object_list(payload.get("tools")),
            provider=to_json_object(provider) if isinstance(provider, dict) else None,
            extra=extra,
        )

    def to_json(self) -> dict[str, JsonValue]:
        payload: dict[str, JsonValue] = {}
        if self.messages:
            payload["messages"] = to_json_value(self.messages)
        if self.model is not None:
            payload["model"] = self.model
        if self.stream is not None:
            payload["stream"] = self.stream
        if self.tool_choice is not None:
            payload["tool_choice"] = self.tool_choice
        if self.tools:
            payload["tools"] = to_json_value(self.tools)
        if self.provider is not None:
            payload["provider"] = self.provider
        if self.extra:
            payload.update(self.extra)
        return payload


@dataclass(slots=True)
class LLMUsagePromptTokenDetails:
    cached_tokens: int = 0
    audio_tokens: int = 0

    @classmethod
    def from_json(cls, payload: Any) -> LLMUsagePromptTokenDetails:
        if not isinstance(payload, dict):
            return cls()
        return cls(
            cached_tokens=coerce_int(payload.get("cached_tokens"), 0),
            audio_tokens=coerce_int(payload.get("audio_tokens"), 0),
        )


@dataclass(slots=True)
class LLMUsageCompletionTokenDetails:
    reasoning_tokens: int = 0
    audio_tokens: int = 0
    accepted_prediction_tokens: int = 0
    rejected_prediction_tokens: int = 0
    image_tokens: int = 0

    @classmethod
    def from_json(cls, payload: Any) -> LLMUsageCompletionTokenDetails:
        if not isinstance(payload, dict):
            return cls()
        return cls(
            reasoning_tokens=coerce_int(payload.get("reasoning_tokens"), 0),
            audio_tokens=coerce_int(payload.get("audio_tokens"), 0),
            accepted_prediction_tokens=coerce_int(
                payload.get("accepted_prediction_tokens"),
                0,
            ),
            rejected_prediction_tokens=coerce_int(
                payload.get("rejected_prediction_tokens"),
                0,
            ),
            image_tokens=coerce_int(payload.get("image_tokens"), 0),
        )


@dataclass(slots=True)
class LLMUsageCostDetails:
    upstream_inference_cost: float = 0.0
    upstream_inference_prompt_cost: float = 0.0
    upstream_inference_completions_cost: float = 0.0

    @classmethod
    def from_json(cls, payload: Any) -> LLMUsageCostDetails:
        if not isinstance(payload, dict):
            return cls()
        return cls(
            upstream_inference_cost=coerce_float(
                payload.get("upstream_inference_cost"),
                0.0,
            ),
            upstream_inference_prompt_cost=coerce_float(
                payload.get("upstream_inference_prompt_cost"),
                0.0,
            ),
            upstream_inference_completions_cost=coerce_float(
                payload.get("upstream_inference_completions_cost"),
                0.0,
            ),
        )


@dataclass(slots=True)
class LLMUsage:
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    prompt_tokens_details: LLMUsagePromptTokenDetails = field(
        default_factory=LLMUsagePromptTokenDetails,
    )
    completion_tokens_details: LLMUsageCompletionTokenDetails = field(
        default_factory=LLMUsageCompletionTokenDetails,
    )
    cost: float = 0.0
    is_byok: bool | None = None
    cost_details: LLMUsageCostDetails = field(default_factory=LLMUsageCostDetails)

    @classmethod
    def from_json(cls, payload: Any) -> LLMUsage:
        if not isinstance(payload, dict):
            return cls()
        is_byok = payload.get("is_byok")
        return cls(
            prompt_tokens=coerce_int(payload.get("prompt_tokens"), 0),
            completion_tokens=coerce_int(payload.get("completion_tokens"), 0),
            total_tokens=coerce_int(payload.get("total_tokens"), 0),
            prompt_tokens_details=LLMUsagePromptTokenDetails.from_json(
                payload.get("prompt_tokens_details")
            ),
            completion_tokens_details=LLMUsageCompletionTokenDetails.from_json(
                payload.get("completion_tokens_details")
            ),
            cost=coerce_float(payload.get("cost"), 0.0),
            is_byok=is_byok if isinstance(is_byok, bool) else None,
            cost_details=LLMUsageCostDetails.from_json(payload.get("cost_details")),
        )

    def to_json(self) -> dict[str, JsonValue]:
        return {
            "prompt_tokens": self.prompt_tokens,
            "completion_tokens": self.completion_tokens,
            "total_tokens": self.total_tokens,
            "prompt_tokens_details": asdict(self.prompt_tokens_details),
            "completion_tokens_details": asdict(self.completion_tokens_details),
            "cost": self.cost,
            "is_byok": self.is_byok,
            "cost_details": asdict(self.cost_details),
        }


@dataclass(slots=True)
class LLMResponse:
    id: str | None = None
    provider: str | None = None
    model: str | None = None
    object: str | None = None
    created: int | None = None
    choices: list[dict[str, JsonValue]] = field(default_factory=list)
    usage: LLMUsage = field(default_factory=LLMUsage)
    status_code: int | None = None
    stream: bool | None = None
    extra: dict[str, JsonValue] = field(default_factory=dict)

    @classmethod
    def from_json(
        cls,
        payload: dict[str, Any],
        *,
        status_code: int | None = None,
        stream: bool | None = None,
    ) -> LLMResponse:
        value_id = payload.get("id")
        provider = payload.get("provider")
        model = payload.get("model")
        object_name = payload.get("object")
        created = payload.get("created")
        known_keys = {
            "id",
            "provider",
            "model",
            "object",
            "created",
            "choices",
            "usage",
            "status_code",
            "stream",
        }
        extra = {
            str(k): to_json_value(v)
            for k, v in payload.items()
            if str(k) not in known_keys
        }
        return cls(
            id=value_id if isinstance(value_id, str) else None,
            provider=provider if isinstance(provider, str) else None,
            model=model if isinstance(model, str) else None,
            object=object_name if isinstance(object_name, str) else None,
            created=coerce_int(created, 0) if created is not None else None,
            choices=to_json_object_list(payload.get("choices")),
            usage=LLMUsage.from_json(payload.get("usage")),
            status_code=status_code,
            stream=stream,
            extra=extra,
        )

    def to_json(self) -> dict[str, JsonValue]:
        payload: dict[str, JsonValue] = {}
        if self.id is not None:
            payload["id"] = self.id
        if self.provider is not None:
            payload["provider"] = self.provider
        if self.model is not None:
            payload["model"] = self.model
        if self.object is not None:
            payload["object"] = self.object
        if self.created is not None:
            payload["created"] = self.created
        if self.choices:
            payload["choices"] = to_json_value(self.choices)
        payload["usage"] = self.usage.to_json()
        if self.status_code is not None:
            payload["status_code"] = self.status_code
        if self.stream is not None:
            payload["stream"] = self.stream
        if self.extra:
            payload.update(self.extra)
        return payload


@dataclass(slots=True)
class LLMParsedMetrics:
    input_tokens: int = 0
    output_tokens: int = 0
    total_tokens: int = 0
    cache_read_tokens: int = 0
    cache_write_tokens: int = 0
    reasoning_tokens: int = 0
    cost: float = 0.0

    @classmethod
    def from_usage(cls, usage: LLMUsage) -> LLMParsedMetrics:
        return cls(
            input_tokens=usage.prompt_tokens,
            output_tokens=usage.completion_tokens,
            total_tokens=usage.total_tokens,
            cache_read_tokens=usage.prompt_tokens_details.cached_tokens,
            reasoning_tokens=usage.completion_tokens_details.reasoning_tokens,
            cost=usage.cost,
        )

    def to_json(self) -> dict[str, JsonValue]:
        return {
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "total_tokens": self.total_tokens,
            "cache_read_tokens": self.cache_read_tokens,
            "cache_write_tokens": self.cache_write_tokens,
            "reasoning_tokens": self.reasoning_tokens,
            "cost": self.cost,
        }


@dataclass(slots=True)
class ToolCallEvent:
    """Tool invocation event captured for one agent run."""

    tool_name: str
    started_at_unix_ms: int
    finished_at_unix_ms: int
    duration_ms: int
    args: list[JsonValue] = field(default_factory=list)
    kwargs: dict[str, JsonValue] = field(default_factory=dict)
    result: JsonValue | None = None
    error: str | None = None

    def to_json(self) -> dict[str, JsonValue]:
        return {
            "tool_name": self.tool_name,
            "started_at_unix_ms": self.started_at_unix_ms,
            "finished_at_unix_ms": self.finished_at_unix_ms,
            "duration_ms": self.duration_ms,
            "args": self.args,
            "kwargs": self.kwargs,
            "result": self.result,
            "error": self.error,
        }


@dataclass(slots=True)
class LLMCallEvent:
    """LLM request/response event captured for one agent run."""

    started_at_unix_ms: int
    finished_at_unix_ms: int
    duration_ms: int
    request: LLMRequest = field(default_factory=LLMRequest)
    response: LLMResponse = field(default_factory=LLMResponse)
    parsed: LLMParsedMetrics = field(default_factory=LLMParsedMetrics)
    error: str | None = None

    def to_json(self) -> dict[str, JsonValue]:
        return {
            "started_at_unix_ms": self.started_at_unix_ms,
            "finished_at_unix_ms": self.finished_at_unix_ms,
            "duration_ms": self.duration_ms,
            "request": self.request.to_json(),
            "response": self.response.to_json(),
            "parsed": self.parsed.to_json(),
            "error": self.error,
        }


@dataclass(slots=True)
class TelemetrySummary:
    model: str | None = None
    tool_calls: int = 0
    failed_tool_calls: int = 0
    llm_calls: int = 0
    failed_llm_calls: int = 0
    llm_input_tokens: int = 0
    llm_output_tokens: int = 0
    llm_total_tokens: int = 0
    llm_cache_read_tokens: int = 0
    llm_cache_write_tokens: int = 0
    llm_reasoning_tokens: int = 0
    llm_cost: float = 0.0
    agent_duration_ms: int = 0

    def to_json(self) -> dict[str, JsonValue]:
        return {
            "model": self.model,
            "tool_calls": self.tool_calls,
            "failed_tool_calls": self.failed_tool_calls,
            "llm_calls": self.llm_calls,
            "failed_llm_calls": self.failed_llm_calls,
            "llm_input_tokens": self.llm_input_tokens,
            "llm_output_tokens": self.llm_output_tokens,
            "llm_total_tokens": self.llm_total_tokens,
            "llm_cache_read_tokens": self.llm_cache_read_tokens,
            "llm_cache_write_tokens": self.llm_cache_write_tokens,
            "llm_reasoning_tokens": self.llm_reasoning_tokens,
            "llm_cost": self.llm_cost,
            "agent_duration_ms": self.agent_duration_ms,
        }


@dataclass(slots=True)
class TelemetryData:
    """Internal per-run telemetry state."""

    trace_id: str
    agent_name: str
    started_at_unix_ms: int
    tool_calls: list[ToolCallEvent] = field(default_factory=list)
    llm_calls: list[LLMCallEvent] = field(default_factory=list)
    finished_at_unix_ms: int | None = None
    duration_ms: int | None = None


@dataclass(slots=True)
class TelemetryPayload(TelemetryData):
    """Serializable telemetry payload captured for one proof-agent run."""

    model: str | None = None
    finished_at_unix_ms: int = 0
    duration_ms: int = 0
    summary: TelemetrySummary = field(default_factory=TelemetrySummary)

    def to_json(self) -> dict[str, JsonValue]:
        payload = asdict(self)
        payload["summary"] = self.summary.to_json()
        payload["tool_calls"] = [call.to_json() for call in self.tool_calls]
        payload["llm_calls"] = [call.to_json() for call in self.llm_calls]
        return payload
