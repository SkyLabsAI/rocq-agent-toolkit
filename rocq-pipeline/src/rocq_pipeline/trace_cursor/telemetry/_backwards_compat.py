"""Backwards compatibility bridge for legacy ``trace_cursor.py`` log payloads.

This helper converts ``InstrumentRocqCursorSpanAttrs`` into the dict shape that
``TracingCursor._trace_log`` used to emit on ``main``, excluding the legacy
``delta`` field.

This file should be deleted ASAP, once ``rocq-agent-toolkit/dashboard/`` has
been ported to use ``InstrumentRocqCursorSpanAttrs`` directly (w/appropriate
generealization for dynamic display logic).
"""

from __future__ import annotations

from typing import Any

from pydantic import BaseModel
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .schema import InstrumentRocqCursorSpanAttrs, LocationInfo


def backwards_compat_payload(
    method: str,
    attrs: InstrumentRocqCursorSpanAttrs,
    *,
    exception: Exception | None = None,
) -> dict[str, Any] | None:
    """Return legacy ``trace_cursor.py`` log kwargs for *method* when possible.

    Returns ``None`` for methods that were not instrumented by
    ``trace_cursor.py`` on ``main``.
    """
    if method not in _LEGACY_METHODS:
        return None

    payload: dict[str, Any] = {
        "before": _location_payload(attrs.before),
        "args": _legacy_args(method, attrs),
    }
    if attrs.action is not None:
        payload["action"] = attrs.action

    if exception is not None:
        payload["exception"] = _legacy_jsonable(exception)
        return payload

    payload["result"] = _legacy_jsonable(attrs.result)
    if attrs.result is not None:
        if attrs.result_type is not None:
            payload["result_type"] = attrs.result_type
        if attrs.error is not None:
            payload["error"] = attrs.error

    if method in _LEGACY_AFTER_METHODS and attrs.after is not None:
        payload["after"] = _location_payload(attrs.after)

    return payload


_LEGACY_METHODS = {
    "RocqCursor.insert_command",
    "RocqCursor.run_step",
    "RocqCursor.query",
    "RocqCursor.query_json",
    "RocqCursor.query_json_all",
    "RocqCursor.query_text",
    "RocqCursor.query_text_all",
    "RocqCursor.revert_before",
    "RocqCursor.advance_to",
    "RocqCursor.go_to",
}

_LEGACY_AFTER_METHODS = {
    "RocqCursor.insert_command",
    "RocqCursor.run_step",
    "RocqCursor.revert_before",
    "RocqCursor.advance_to",
    "RocqCursor.go_to",
}


def _legacy_jsonable(value: Any) -> Any:
    if value is None:
        return {}
    if isinstance(value, BaseModel):
        return value.model_dump()
    if isinstance(value, rdm_api.Err):
        return {"message": value.message, "data": _legacy_jsonable(value.data)}
    if hasattr(value, "to_json"):
        return value.to_json()
    if isinstance(value, list):
        return [_legacy_jsonable(v) for v in value]
    if isinstance(value, dict):
        return {str(k): _legacy_jsonable(v) for k, v in value.items()}
    if isinstance(value, (str, int, float)):
        return value
    return {}


def _location_payload(location: LocationInfo | None) -> dict[str, Any]:
    if location is None:
        return {}
    return location.model_dump(mode="json", exclude_none=True)


def _legacy_args(method: str, attrs: InstrumentRocqCursorSpanAttrs) -> Any:
    args = attrs.args
    assert isinstance(args, dict)
    if method == "RocqCursor.insert_command":
        assert "text" in args
        text = args["text"]
        ghost = bool(args.get("ghost", False))
        return (text, ghost)
    if method == "RocqCursor.run_step":
        return attrs.action
    if method in {
        "RocqCursor.query",
        "RocqCursor.query_json_all",
        "RocqCursor.query_text_all",
    }:
        assert "text" in args
        return args["text"]
    return args
