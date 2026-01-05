"""
Tempo/Loki helper utilities for the dashboard visualizer.

This is intentionally "thin":
- Tempo is queried for traces/search
- Loki is queried for logs
- We also expose helpers to extract spans from Tempo OTLP-ish JSON so the frontend
  can build service/span graphs consistently.
"""

from __future__ import annotations

import base64
import logging
from datetime import UTC, datetime
from typing import Any

import httpx
from fastapi import HTTPException

from backend.config import settings
from backend.models import VisualizerSpanLite

logger = logging.getLogger(__name__)


def _otel_value(v: Any) -> Any:
    if not isinstance(v, dict):
        return v
    # OTLP AnyValue is a oneof
    for k in (
        "stringValue",
        "intValue",
        "doubleValue",
        "boolValue",
        "bytesValue",
        "arrayValue",
        "kvlistValue",
    ):
        if k in v:
            return v[k]
    return v


def _attrs_to_dict(attrs: list[dict[str, Any]] | None) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for a in attrs or []:
        key = a.get("key")
        if not key:
            continue
        out[str(key)] = _otel_value(a.get("value"))
    return out


def _b64_to_hex(s: str | None) -> str | None:
    if not s:
        return None
    # Tempo trace JSON often includes IDs as base64-encoded bytes.
    # If the string looks like hex already, keep it.
    hex_chars = set("0123456789abcdefABCDEF")
    if len(s) in (16, 32) and all(c in hex_chars for c in s):
        return s.lower()
    try:
        raw = base64.b64decode(s, validate=False)
        return raw.hex()
    except Exception:
        return s


def extract_spans_best_effort(
    trace_id: str, raw_trace: dict[str, Any]
) -> list[VisualizerSpanLite]:
    """
    Converting the raw tempo trace json to a list of VisualizerSpanLite objects.
    Here we are added if conditions to support the v2 format of the API response as well.
    """

    spans: list[VisualizerSpanLite] = []
    batches = (
        raw_trace.get("batches")
        or raw_trace.get("trace", {}).get("resourceSpans", [])
        or []
    )
    if not isinstance(batches, list):
        return spans

    for batch in batches:
        if not isinstance(batch, dict):
            continue
        resource = batch.get("resource") or {}
        resource_attrs = _attrs_to_dict(resource.get("attributes") or [])

        scopes = (
            batch.get("scopeSpans") or batch.get("instrumentationLibrarySpans") or []
        )
        if not isinstance(scopes, list):
            continue

        for scope in scopes:
            if not isinstance(scope, dict):
                continue
            otel_spans = scope.get("spans") or []
            if not isinstance(otel_spans, list):
                continue

            for sp in otel_spans:
                if not isinstance(sp, dict):
                    continue

                span_id = _b64_to_hex(sp.get("spanId") or sp.get("spanID") or "")
                if not span_id:
                    continue
                parent_span_id = _b64_to_hex(
                    sp.get("parentSpanId") or sp.get("parentSpanID")
                )
                name = str(sp.get("name") or "span")

                start_ns = sp.get("startTimeUnixNano")
                end_ns = sp.get("endTimeUnixNano")
                span_attrs = _attrs_to_dict(sp.get("attributes") or [])
                status = sp.get("status") or {}

                service_name = (
                    str(
                        resource_attrs.get("service.name")
                        or resource_attrs.get("service_name")
                        or ""
                    )
                    or str(
                        span_attrs.get("service.name")
                        or span_attrs.get("service_name")
                        or ""
                    )
                    or "unknown"
                )

                spans.append(
                    VisualizerSpanLite(
                        trace_id=trace_id,
                        span_id=span_id,
                        parent_span_id=parent_span_id or None,
                        name=name,
                        service_name=service_name,
                        status=status or None,
                        start_time_unix_nano=str(start_ns)
                        if start_ns is not None
                        else None,
                        end_time_unix_nano=str(end_ns) if end_ns is not None else None,
                        attributes={**resource_attrs, **span_attrs},
                    )
                )

    return spans


async def tempo_get_trace(trace_id: str) -> dict[str, Any]:
    """
    Fetch raw trace data from Tempo.

    Returns a dict following the OTLP JSON format (Tempo API).

    Example of the returned structure:
    ```json
    {
      "batches": [
        {
          "resource": {
            "attributes": [
              {
                "key": "service.name",
                "value": { "stringValue": "rocq_agent" }
              }
            ]
          },
          "scopeSpans": [
            {
              "scope": { "name": "observability.tracing.decorators" },
              "spans": [
                {
                  "traceId": "Y23/W6wzPgKMSGGVtudxnA==", # in base 64 encoding
                  "spanId": "HHw2Q53cxFY=", # in base 64 encoding
                  "name": "Running pipeline",
                  "kind": "SPAN_KIND_INTERNAL",
                  "startTimeUnixNano": "1767604618978642115",
                  "endTimeUnixNano": "1767604655930397084",
                  "attributes": [
                    {
                      "key": "run.id",
                      "value": { "stringValue": "cb1b04cc-..." }
                    }
                  ],
                  "status": { "code": "STATUS_CODE_OK" }
                }
              ]
            }
          ]
        }
      ]
    }
    ```
    """
    url = f"{settings.tempo_url}/api/traces/{trace_id}"
    async with httpx.AsyncClient(timeout=30.0) as client:
        resp = await client.get(url)
    if resp.status_code == 404:
        raise HTTPException(status_code=404, detail=f"Trace not found: {trace_id}")
    if resp.status_code >= 400:
        raise HTTPException(status_code=502, detail=f"Tempo error ({resp.status_code})")
    return resp.json()


async def loki_query_range(
    *,
    query: str,
    start: datetime,
    end: datetime,
    limit: int,
    direction: str,
) -> dict[str, Any]:
    loki_url = f"{settings.observability_url}/loki/api/v1/query_range"
    params: dict[str, str | int] = {
        "query": query,
        "start": start.astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "end": end.astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "limit": limit,
        "direction": direction,
    }
    try:
        async with httpx.AsyncClient(timeout=30.0) as client:
            resp = await client.get(loki_url, params=params)
        resp.raise_for_status()
        return resp.json()
    except httpx.HTTPStatusError as e:
        logger.error("Loki HTTP error: %s", e)
        raise HTTPException(
            status_code=502, detail=f"Loki error ({e.response.status_code})"
        ) from e
    except httpx.RequestError as e:
        logger.error("Loki request error: %s", e)
        raise HTTPException(
            status_code=503,
            detail=f"Could not connect to Loki at {settings.observability_url}",
        ) from e
