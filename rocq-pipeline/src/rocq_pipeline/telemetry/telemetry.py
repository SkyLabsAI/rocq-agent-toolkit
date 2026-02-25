from __future__ import annotations

import copy
import gzip
import json
import os
import uuid
import zlib
from collections.abc import AsyncIterator, Callable
from contextlib import asynccontextmanager
from contextvars import ContextVar
from datetime import UTC, datetime
from functools import wraps
from pathlib import Path
from typing import Any

import httpx
from observability import get_logger

from .models import (
    LLMCallEvent,
    LLMParsedMetrics,
    LLMRequest,
    LLMResponse,
    TelemetryData,
    TelemetryPayload,
    TelemetrySummary,
    ToolCallEvent,
    coerce_float,
    to_json_object,
    to_json_value,
)

logger = get_logger("rocq_agent.telemetry")


_current_telemetry_run: ContextVar[TelemetryData | None] = ContextVar(
    "rocq_telemetry_run",
    default=None,
)


def _unix_now_ms() -> int:
    return int(datetime.now(UTC).timestamp() * 1000)


def _duration_ms(start_ms: int, end_ms: int) -> int:
    return max(0, end_ms - start_ms)


@asynccontextmanager
async def telemetry_run(
    agent_name: str,
    trace_id: str | None = None,
) -> AsyncIterator[TelemetryData]:
    """Create per-run telemetry context and cleanly reset it after run end."""
    run = TelemetryData(
        run_uid=trace_id if trace_id else str(uuid.uuid4()),
        agent_name=agent_name,
        started_at_unix_ms=_unix_now_ms(),
    )
    token = _current_telemetry_run.set(run)
    try:
        yield run
    finally:
        _current_telemetry_run.reset(token)


def instrument_tool_call(fn: Callable[..., Any]) -> Callable[..., Any]:
    """Decorator for async tools to record args/result/duration in current run."""

    @wraps(fn)
    async def wrapped(*args: Any, **kwargs: Any) -> Any:
        run = _current_telemetry_run.get()
        started_at_unix_ms = _unix_now_ms()
        error: str | None = None
        result: Any = None
        try:
            result = await fn(*args, **kwargs)
            return result
        except Exception as exc:
            error = f"{type(exc).__name__}: {exc}"
            raise
        finally:
            if run is not None:
                finished_at_unix_ms = _unix_now_ms()
                serialized_args: list[Any] = []
                for arg in args:
                    # RunContext and SDK objects are noisy/non-serializable.
                    if hasattr(arg, "deps") and arg.__class__.__name__ == "RunContext":
                        serialized_args.append({"type": "RunContext"})
                    else:
                        serialized_args.append(to_json_value(arg))

                run.tool_calls.append(
                    ToolCallEvent(
                        tool_name=fn.__name__,
                        started_at_unix_ms=started_at_unix_ms,
                        finished_at_unix_ms=finished_at_unix_ms,
                        duration_ms=_duration_ms(
                            started_at_unix_ms, finished_at_unix_ms
                        ),
                        args=serialized_args,
                        kwargs=to_json_object(dict(kwargs)),
                        result=to_json_value(result),
                        error=error,
                    )
                )

    return wrapped


def process_llm_request_data(
    req_data: dict[str, Any],
    is_first_call: bool,
    keep_full_payload: bool = False,
    log_first_system_prompt: bool = True,
    log_first_tools: bool = True,
) -> LLMRequest:
    """Compress LLM request payloads to avoid repetitive logs.
    Since LLM requests Contain the complete chat history, each time,
    we process it to avoid repetitive logs."""

    req_copy = copy.deepcopy(req_data)

    if keep_full_payload:
        return LLMRequest.from_json(req_copy)

    # Keep tools only on the first call unless explicitly configured otherwise.
    if not (is_first_call and log_first_tools):
        req_copy.pop("tools", None)

    messages = req_copy.get("messages")
    if isinstance(messages, list):
        filtered_msgs = []
        for msg in messages:
            if not isinstance(msg, dict):
                continue
            if msg.get("role") == "system" and not (
                is_first_call and log_first_system_prompt
            ):
                continue
            filtered_msgs.append(msg)

        system_msgs = [m for m in filtered_msgs if m.get("role") == "system"]
        other_msgs = [m for m in filtered_msgs if m.get("role") != "system"]

        final_msgs = system_msgs
        if other_msgs:
            final_msgs.append(other_msgs[-1])

        req_copy["messages"] = final_msgs

    return LLMRequest.from_json(req_copy)


def process_llm_response_data(
    resp_data: dict[str, Any],
    keep_full_payload: bool = False,
) -> LLMResponse:
    """Compress LLM responses by removing bulky non-essential fields.
    Right now, It is just removing the reasoning_details hashes
    """

    if keep_full_payload:
        return LLMResponse.from_json(resp_data)

    resp_copy = copy.deepcopy(resp_data)
    choices = resp_copy.get("choices")
    if isinstance(choices, list):
        for choice in choices:
            if not isinstance(choice, dict):
                continue
            message = choice.get("message", {})
            if isinstance(message, dict):
                message.pop("reasoning_details", None)

    return LLMResponse.from_json(resp_copy)


def record_llm_call_event(event: LLMCallEvent) -> None:
    """Append an LLM telemetry event to the current run, if one exists."""
    run = _current_telemetry_run.get()
    if run is None:
        return

    run.llm_calls.append(event)


def _decode_response_body(body_bytes: bytes, content_encoding: str) -> bytes:
    encoding = content_encoding.lower()
    if "gzip" in encoding:
        return gzip.decompress(body_bytes)
    if "deflate" in encoding:
        try:
            return zlib.decompress(body_bytes)
        except zlib.error:
            return zlib.decompress(body_bytes, -zlib.MAX_WBITS)
    return body_bytes


class _InterceptingStream(httpx.AsyncByteStream):
    def __init__(
        self, stream: httpx.AsyncByteStream, callback: Callable[[bytes], None]
    ):
        self.stream = stream
        self.callback = callback
        self.body = bytearray()

    async def __aiter__(self) -> AsyncIterator[bytes]:
        async for chunk in self.stream:
            self.body.extend(chunk)
            yield chunk

    async def aclose(self) -> None:
        await self.stream.aclose()
        self.callback(bytes(self.body))


class OpenAITelemetryTransport(httpx.AsyncBaseTransport):
    """Intercept OpenAI-formatted request/response traffic and log telemetry."""

    def __init__(self, underlying: httpx.AsyncBaseTransport):
        self.underlying = underlying

    async def handle_async_request(self, request: httpx.Request) -> httpx.Response:
        run = _current_telemetry_run.get()
        started_at_unix_ms = _unix_now_ms()

        req_data: dict[str, Any] = {}
        if run is not None and request.content:
            try:
                req_data = json.loads(request.content.decode("utf-8"))
            except Exception:
                req_data = {}

        response = await self.underlying.handle_async_request(request)

        if run is not None and req_data and response.status_code == 200:

            def on_close(body_bytes: bytes) -> None:
                finished_at_unix_ms = _unix_now_ms()
                duration_ms = _duration_ms(started_at_unix_ms, finished_at_unix_ms)
                is_first_call = len(run.llm_calls) == 0
                compressed_req_data = process_llm_request_data(
                    req_data, is_first_call, log_first_system_prompt=False
                )

                try:
                    if req_data.get("stream", False):
                        record_llm_call_event(
                            LLMCallEvent(
                                started_at_unix_ms=started_at_unix_ms,
                                finished_at_unix_ms=finished_at_unix_ms,
                                duration_ms=duration_ms,
                                request=compressed_req_data,
                                response=LLMResponse(
                                    status_code=response.status_code,
                                    stream=True,
                                ),
                                parsed=LLMParsedMetrics(),
                            )
                        )
                        return

                    decoded_body = _decode_response_body(
                        body_bytes,
                        response.headers.get("content-encoding", ""),
                    )
                    raw_resp_data = json.loads(decoded_body.decode("utf-8"))
                    resp_data = raw_resp_data if isinstance(raw_resp_data, dict) else {}
                    parsed_response = process_llm_response_data(resp_data)
                    parsed_metrics = LLMParsedMetrics.from_usage(parsed_response.usage)
                    record_llm_call_event(
                        LLMCallEvent(
                            started_at_unix_ms=started_at_unix_ms,
                            finished_at_unix_ms=finished_at_unix_ms,
                            duration_ms=duration_ms,
                            request=compressed_req_data,
                            response=parsed_response,
                            parsed=parsed_metrics,
                        )
                    )
                except Exception as exc:
                    logger.warning(
                        "Failed to parse LLM telemetry response", error=str(exc)
                    )
                    record_llm_call_event(
                        LLMCallEvent(
                            started_at_unix_ms=started_at_unix_ms,
                            finished_at_unix_ms=finished_at_unix_ms,
                            duration_ms=duration_ms,
                            request=compressed_req_data,
                            response=LLMResponse(status_code=response.status_code),
                            parsed=LLMParsedMetrics(),
                            error=f"telemetry_parse_error: {type(exc).__name__}: {exc}",
                        )
                    )

            if isinstance(response.stream, httpx.AsyncByteStream):
                response.stream = _InterceptingStream(response.stream, on_close)
            else:
                logger.debug(
                    "Skipping LLM telemetry stream interception for sync stream",
                    stream_type=type(response.stream).__name__,
                )

        return response


def _build_summary(run: TelemetryData) -> TelemetrySummary:
    parsed_usage = [call.parsed for call in run.llm_calls]
    return TelemetrySummary(
        tool_calls=len(run.tool_calls),
        failed_tool_calls=len([call for call in run.tool_calls if call.error]),
        llm_calls=len(run.llm_calls),
        failed_llm_calls=len([call for call in run.llm_calls if call.error]),
        llm_input_tokens=sum(metric.input_tokens for metric in parsed_usage),
        llm_output_tokens=sum(metric.output_tokens for metric in parsed_usage),
        llm_total_tokens=sum(metric.total_tokens for metric in parsed_usage),
        llm_cache_read_tokens=sum(metric.cache_read_tokens for metric in parsed_usage),
        llm_cache_write_tokens=sum(
            metric.cache_write_tokens for metric in parsed_usage
        ),
        llm_reasoning_tokens=sum(metric.reasoning_tokens for metric in parsed_usage),
        llm_cost=sum(coerce_float(metric.cost, 0.0) for metric in parsed_usage),
        agent_duration_ms=run.duration_ms or 0,
    )


def current_telemetry_payload() -> TelemetryPayload | None:
    """Materialize current run telemetry as a typed payload."""
    run = _current_telemetry_run.get()
    if run is None:
        return None

    if run.finished_at_unix_ms is None:
        run.finished_at_unix_ms = _unix_now_ms()
    if run.duration_ms is None:
        run.duration_ms = _duration_ms(run.started_at_unix_ms, run.finished_at_unix_ms)

    return TelemetryPayload(
        run_uid=run.run_uid,
        agent_name=run.agent_name,
        started_at_unix_ms=run.started_at_unix_ms,
        tool_calls=list(run.tool_calls),
        llm_calls=list(run.llm_calls),
        finished_at_unix_ms=run.finished_at_unix_ms,
        duration_ms=run.duration_ms,
        summary=_build_summary(run),
    )


# TODO: Remove this
def append_telemetry_jsonl(payload: TelemetryPayload) -> str:
    """Append telemetry payload to a JSONL file and return the file path."""
    path_from_env = os.getenv("ROCQ_TELEMETRY_JSONL")
    output_path = (
        Path(path_from_env) if path_from_env else Path.cwd() / "rocq_telemetry.jsonl"
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("a", encoding="utf8") as file:
        json.dump(payload.to_json(), file, ensure_ascii=True)
        file.write("\n")

    logger.info("Telemetry appended", path=str(output_path))
    return str(output_path)
