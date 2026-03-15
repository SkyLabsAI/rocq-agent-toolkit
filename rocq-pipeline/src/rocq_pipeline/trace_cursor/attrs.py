"""Typed pydantic schema for ``TracingCursor`` span attributes.

This module defines the structured attribute model that ``_trace`` in
``cursor.py`` accumulates during execution and flushes to the OTel span.
The same model is used by downstream consumers (e.g. ``dashboard/backend``) to
deserialize span attribute dicts back into typed objects.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

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

SCHEMA_FILENAME = f"TraceCursorSpanAttrs.v{SCHEMA_VERSION}.json"


class LocationInfo(BaseModel):
    """Cursor location snapshot: content-hash id and optional proof goal."""

    id: str
    goal: str | None = None


class TraceCursorSpanAttrs(BaseModel):
    """Span attributes emitted by ``TracingCursor`` methods.

    ``extra="ignore"`` ensures forwards compatibility: consumers running an
    older schema version silently drop unknown fields added in newer versions.
    """

    model_config = ConfigDict(extra="ignore")

    args: Any | None = Field(default_factory=dict)
    action: str | None = None
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
    """Write the ``TraceCursorSpanAttrs`` JSON schema to *schemas_dir*.

    Defaults to ``tests/schemas/`` relative to the working directory.

    If the target file already exists and its contents match, this is a no-op.
    If the file exists but contents **differ**, raises ``SystemExit`` — bump
    ``SCHEMA_VERSION`` before persisting a breaking change.
    """
    if schemas_dir is None:
        schemas_dir = Path("tests/schemas")

    target = schemas_dir / SCHEMA_FILENAME
    current = (
        json.dumps(TraceCursorSpanAttrs.model_json_schema(), sort_keys=True, indent=2)
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
    """CLI entry point (``persist-trace-cursor-schema``)."""
    schemas_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    persist_schema(schemas_dir)
