"""Typed pydantic schema for ``InstrumentRocqCursor`` span attributes.

This module defines the structured attribute model that ``InstrumentRocqCursor``
accumulates during execution and flushes to the OTel span (via
``model_dump(mode="json")`` / ``model_as_otel_attrs``).

The dashboard tactic graph (``dashboard/backend`` ``build_rocq_cursor_graph``)
consumes **Loki log lines**: structured JSON merged with stream labels, not a
round-trip through this model. Optional future work could deserialize span
attributes with ``model_from_otel_attrs`` where Tempo data is the source of truth.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Literal

from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    JsonValue,
    SerializerFunctionWrapHandler,
    field_serializer,
)
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

SCHEMA_VERSION: str = "0.1.0"

SCHEMA_FILENAME = f"InstrumentRocqCursorSpanAttrs.v{SCHEMA_VERSION}.json"


class LocationInfo(BaseModel):
    """Cursor location snapshot: content-hash id and optional proof goal."""

    id: str
    goal: str | None = None


class InstrumentRocqCursorSpanAttrs(BaseModel):
    """Span attributes emitted by instrumented methods RocqCursor.

    Attributes:
    - args (always): the arguments used to call the method
    - action (success; optional): the /single/ (parseable) doc interaction for the method
    - action_kind (success; w/`action`): the /kind/ of `action`, one of:
      + `"blanks"`: insert a single Rocq blank (e.g. whitespace or comment)
      + `"command"`: insert a single Rocq command
      + `"ghost"`: run a single Rocq command, but don't insert it
    - before (success; always): the `LocationInfo` before the method is invoked
    - after (success; optional): the `LocationInfo` after an effectful method is invoked
    - error (success; always): whether or not the method resulted in an exception/error
    - result (success; always): the value returned
    - result_type (success; w/`result`): the name of the result-value type

    The `InstrumentRocqCursor` class (cf. `./instrumentation.py`) uses
    `auto_instrument_skip_value` to determine whether or not arg/result values
    should be included.

    To avoid double counting document interactions, only low-level operations
    that produce individual document modifications track `action` & `action_kind`.
    Composite actions which produce multiple document effects will still have a
    non-`None` value for `after`, but child spans will need to be inspected to
    access/accumulate the multiple `action`+`action_kind` pairs.

    In case of exception/error (reflected via the span status & `error` attr), some
    of the attributes may be missing.

    Note: ``extra="ignore"`` ensures forwards compatibility: consumers running an
    older schema version silently drop unknown fields added in newer versions.
    """

    model_config = ConfigDict(extra="ignore")

    args: Any | None = Field(default_factory=dict)
    action: str | None = None
    action_kind: Literal["blanks", "command", "ghost"] | None = None
    before: LocationInfo | None = None
    after: LocationInfo | None = None
    error: bool | None = None
    result: Any | None = None
    result_type: str | None = None

    # TODO: remove the following serialization logic when ocaml-jsonrpc-tp/python
    # changes Err+Resp types to be BaseModels.
    @field_serializer("result", mode="wrap")
    @classmethod
    def serialize_result(
        cls, result: Any, handler: SerializerFunctionWrapHandler
    ) -> JsonValue:
        if isinstance(result, (rdm_api.Err, rdm_api.Resp)):
            return result.to_json()
        else:
            return handler(result)


def persist_schema(schemas_dir: Path | None = None) -> None:
    """Write the ``InstrumentRocqCursorSpanAttrs`` JSON schema to *schemas_dir*.

    Defaults to `$PWD/.schemas`.

    If the target file already exists and its contents match, this is a no-op.
    If the file exists but contents **differ**, raises ``SystemExit`` — bump
    ``SCHEMA_VERSION`` before persisting a breaking change.
    """
    if schemas_dir is None:
        schemas_dir = Path(__file__).parent / ".schemas"

    target = schemas_dir / SCHEMA_FILENAME
    current = (
        json.dumps(
            InstrumentRocqCursorSpanAttrs.model_json_schema(), sort_keys=True, indent=2
        )
        + "\n"
    )

    if target.exists():
        if target.read_text() == current:
            print(f"Up-to-date: {target}")
            return
        raise SystemExit(
            f"Schema drift: {target} exists but contents differ from the "
            f"current model.  Bump SCHEMA_VERSION before persisting."
        )

    schemas_dir.mkdir(parents=True, exist_ok=True)
    target.write_text(current)
    print(f"Wrote: {target}")


def main() -> None:
    """CLI entry point (``persist-instrument-rocq-cursor-schema``)."""
    schemas_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    persist_schema(schemas_dir)
