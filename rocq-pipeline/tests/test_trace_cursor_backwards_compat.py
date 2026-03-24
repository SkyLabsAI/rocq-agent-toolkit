from __future__ import annotations

from rocq_pipeline.trace_cursor.telemetry._backwards_compat import (
    backwards_compat_payload,
)
from rocq_pipeline.trace_cursor.telemetry.schema import (
    InstrumentRocqCursorSpanAttrs,
    LocationInfo,
)


def test_backwards_compat_query_success_shape() -> None:
    attrs = InstrumentRocqCursorSpanAttrs(
        args={"text": "About nat."},
        before=LocationInfo(id="before-id"),
        error=False,
        result="ok",
        result_type="<class 'str'>",
    )

    payload = backwards_compat_payload("RocqCursor.query", attrs)

    assert payload == {
        "before": {"id": "before-id"},
        "args": "About nat.",
        "result": "ok",
        "result_type": "<class 'str'>",
        "error": False,
    }


def test_backwards_compat_insert_command_success_shape() -> None:
    attrs = InstrumentRocqCursorSpanAttrs(
        args={"text": "exact I.", "ghost": False},
        action="exact I.",
        before=LocationInfo(id="before-id"),
        after=LocationInfo(id="after-id"),
        error=False,
        result=None,
    )

    payload = backwards_compat_payload("RocqCursor.insert_command", attrs)

    assert payload == {
        "before": {"id": "before-id"},
        "args": ("exact I.", False),
        "action": "exact I.",
        "result": {},
        "after": {"id": "after-id"},
    }
    assert "delta" not in payload


def test_backwards_compat_exception_shape() -> None:
    attrs = InstrumentRocqCursorSpanAttrs(
        args={},
        before=LocationInfo(id="before-id"),
        error=True,
    )

    payload = backwards_compat_payload(
        "RocqCursor.run_step",
        attrs,
        exception=RuntimeError("boom"),
    )

    assert payload is not None
    assert payload["before"] == {"id": "before-id"}
    assert payload["args"] is None
    assert payload["exception"] == {}
    assert "result" not in payload
    assert "after" not in payload


def test_backwards_compat_returns_none_for_non_legacy_method() -> None:
    attrs = InstrumentRocqCursorSpanAttrs(
        args={},
        before=LocationInfo(id="before-id"),
        error=False,
    )
    payload = backwards_compat_payload("RocqCursor.load_file", attrs)
    assert payload is None
