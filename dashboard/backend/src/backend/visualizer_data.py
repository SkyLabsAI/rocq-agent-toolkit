"""
Visualizer Data API

Stable API surface for the dashboard visualizer UI under:

  /visualizer/data/*
"""

from __future__ import annotations

import json
from datetime import UTC, datetime, timedelta
from typing import Any

from fastapi import APIRouter, Body, Query

from backend.models import (
    VisualizerServiceGraphResponse,
    VisualizerServicesResponse,
    VisualizerSpanGraphResponse,
    VisualizerSpanLite,
    VisualizerSpansResponse,
    VisualizerTraceIdsResponse,
)
from backend.visualizer import extract_spans_best_effort, loki_query_range, tempo_get_trace, tempo_search

router = APIRouter(prefix="/visualizer/data", tags=["visualizer"])


@router.get("/tempo/search")
async def visualizer_data_tempo_search(
    q: str = Query(default="{}", description="TraceQL query"),
    start_s: int = Query(..., description="Start time (unix seconds)"),
    end_s: int = Query(..., description="End time (unix seconds)"),
    limit: int = Query(default=20, ge=1, le=200),
) -> dict[str, Any]:
    return await tempo_search(q=q, start_s=start_s, end_s=end_s, limit=limit)


@router.get("/tempo/search/ids")
async def visualizer_data_tempo_search_ids(
    q: str = Query(default="{}", description="TraceQL query"),
    start_s: int = Query(..., description="Start time (unix seconds)"),
    end_s: int = Query(..., description="End time (unix seconds)"),
    limit: int = Query(default=20, ge=1, le=200),
) -> dict[str, Any]:
    raw = await tempo_search(q=q, start_s=start_s, end_s=end_s, limit=limit)
    traces = raw.get("traces") or (raw.get("data", {}) or {}).get("traces") or []
    trace_ids = []
    for t in traces:
        if isinstance(t, dict) and isinstance(t.get("traceID"), str):
            trace_ids.append(t["traceID"])
    return {"trace_ids": trace_ids, "total": len(trace_ids)}


@router.get("/tempo/traces/{trace_id}")
async def visualizer_data_tempo_trace(trace_id: str) -> dict[str, Any]:
    return await tempo_get_trace(trace_id)


@router.get("/tempo/traces/{trace_id}/spans", response_model=VisualizerSpansResponse)
async def visualizer_data_tempo_trace_spans(trace_id: str) -> VisualizerSpansResponse:
    raw = await tempo_get_trace(trace_id)
    spans = extract_spans_best_effort(trace_id, raw)
    return VisualizerSpansResponse(spans=[VisualizerSpanLite(**s.__dict__) for s in spans])


@router.post("/spans", response_model=VisualizerSpansResponse)
async def visualizer_data_spans_from_traces(
    trace_ids: list[str] = Body(..., embed=True, description="Tempo trace ids (hex)"),
    service_name: str | None = Query(default=None),
) -> VisualizerSpansResponse:
    all_spans = []
    for tid in trace_ids:
        raw = await tempo_get_trace(tid)
        all_spans.extend(extract_spans_best_effort(tid, raw))
    if service_name:
        all_spans = [s for s in all_spans if s.service_name == service_name]
    return VisualizerSpansResponse(spans=[VisualizerSpanLite(**s.__dict__) for s in all_spans])


@router.get("/loki/query_range")
async def visualizer_data_loki_query_range(
    query: str = Query(...),
    start_ms: int = Query(..., description="Start ms since epoch"),
    end_ms: int = Query(..., description="End ms since epoch"),
    limit: int = Query(default=200, ge=1, le=5000),
    direction: str = Query(default="backward", pattern="^(backward|forward)$"),
) -> dict[str, Any]:
    start = datetime.fromtimestamp(start_ms / 1000, tz=UTC)
    end = datetime.fromtimestamp(end_ms / 1000, tz=UTC)
    return await loki_query_range(query=query, start=start, end=end, limit=limit, direction=direction)


@router.get("/logs/by-span")
async def visualizer_data_logs_by_span(
    *,
    service: str = Query(..., description="Service label value"),
    trace_id: str = Query(...),
    span_id: str = Query(...),
    start_ms: int = Query(..., description="Start ms since epoch"),
    end_ms: int = Query(..., description="End ms since epoch"),
    limit: int = Query(default=200, ge=1, le=5000),
    direction: str = Query(default="backward", pattern="^(backward|forward)$"),
    service_label: str = Query(default="service_name", description="Loki label key for service"),
    trace_id_field: str = Query(default="trace_id", description="JSON field for trace id"),
    span_id_field: str = Query(default="span_id", description="JSON field for span id"),
) -> dict[str, Any]:
    start = datetime.fromtimestamp(start_ms / 1000, tz=UTC)
    end = datetime.fromtimestamp(end_ms / 1000, tz=UTC)
    logql = (
        f'{{{service_label}="{service}"}} | json '
        f'| {trace_id_field}="{trace_id}" '
        f'| {span_id_field}="{span_id}"'
    )
    return await loki_query_range(query=logql, start=start, end=end, limit=limit, direction=direction)


@router.get("/runs/{run_id}/trace-ids", response_model=VisualizerTraceIdsResponse)
async def visualizer_data_trace_ids_for_run(
    run_id: str,
    limit: int = Query(default=50, ge=1, le=500, description="Max unique trace ids to return"),
    service_label: str = Query(default="service_name"),
    service_value: str = Query(default="rocq_agent"),
    trace_id_field: str = Query(default="trace_id"),
    start_ms: int | None = Query(default=None, description="Start ms since epoch"),
    end_ms: int | None = Query(default=None, description="End ms since epoch"),
    lookback_minutes: int | None = Query(default=None, ge=1, le=60 * 24 * 7),
    lookback_hours: int = Query(default=24, ge=1, le=24 * 30),
) -> VisualizerTraceIdsResponse:
    if start_ms is not None and end_ms is not None:
        start = datetime.fromtimestamp(start_ms / 1000, tz=UTC)
        end = datetime.fromtimestamp(end_ms / 1000, tz=UTC)
    else:
        end = datetime.now(UTC)
        if lookback_minutes is not None:
            start = end - timedelta(minutes=lookback_minutes)
        else:
            start = end - timedelta(hours=lookback_hours)

    logql = f'{{{service_label}="{service_value}"}} | json | run_id="{run_id}"'
    data = await loki_query_range(query=logql, start=start, end=end, limit=5000, direction="backward")
    trace_ids: set[str] = set()

    for stream in data.get("data", {}).get("result", []) or []:
        for _ts_ns, line in stream.get("values", []) or []:
            try:
                obj = json.loads(line)
            except Exception:
                continue
            tid = obj.get(trace_id_field) or obj.get("otelTraceID") or obj.get("trace_id")
            if isinstance(tid, str) and tid:
                trace_ids.add(tid)
            if len(trace_ids) >= limit:
                break
        if len(trace_ids) >= limit:
            break

    out = sorted(trace_ids)
    return VisualizerTraceIdsResponse(run_id=run_id, trace_ids=out, total=len(out))


@router.post("/services", response_model=VisualizerServicesResponse)
async def visualizer_data_services_from_traces(
    trace_ids: list[str] = Body(..., embed=True, description="Tempo trace ids (hex)"),
) -> VisualizerServicesResponse:
    all_spans = []
    for tid in trace_ids:
        raw = await tempo_get_trace(tid)
        all_spans.extend(extract_spans_best_effort(tid, raw))

    agg: dict[str, dict[str, Any]] = {}
    for s in all_spans:
        cur = agg.get(s.service_name) or {"span_count": 0, "trace_ids": set()}
        cur["span_count"] += 1
        cur["trace_ids"].add(s.trace_id)
        agg[s.service_name] = cur

    services = [
        {"service_name": svc, "span_count": v["span_count"], "trace_count": len(v["trace_ids"])}
        for svc, v in agg.items()
    ]
    services.sort(key=lambda x: x["span_count"], reverse=True)
    return VisualizerServicesResponse(services=services)


@router.post("/graphs/service", response_model=VisualizerServiceGraphResponse)
async def visualizer_data_service_graph(
    trace_ids: list[str] = Body(..., embed=True, description="Tempo trace ids (hex)"),
    min_edge_count: int = Query(default=1, ge=1, le=100),
) -> VisualizerServiceGraphResponse:
    all_spans = []
    for tid in trace_ids:
        raw = await tempo_get_trace(tid)
        all_spans.extend(extract_spans_best_effort(tid, raw))

    by_span_id = {s.span_id: s for s in all_spans}
    node_agg: dict[str, dict[str, Any]] = {}
    edge_agg: dict[str, dict[str, Any]] = {}

    for s in all_spans:
        n = node_agg.get(s.service_name) or {"span_count": 0, "trace_ids": set()}
        n["span_count"] += 1
        n["trace_ids"].add(s.trace_id)
        node_agg[s.service_name] = n

        if not s.parent_span_id:
            continue
        parent = by_span_id.get(s.parent_span_id)
        if not parent:
            continue
        if parent.service_name == s.service_name:
            continue
        key = f"{parent.service_name}→{s.service_name}"
        e = edge_agg.get(key) or {"source": parent.service_name, "target": s.service_name, "count": 0}
        e["count"] += 1
        edge_agg[key] = e

    nodes = [
        {"id": svc, "service": svc, "span_count": v["span_count"], "trace_count": len(v["trace_ids"])}
        for svc, v in node_agg.items()
    ]
    edges = [
        {"id": k, "source": v["source"], "target": v["target"], "count": v["count"]}
        for k, v in edge_agg.items()
        if v["count"] >= min_edge_count
    ]
    nodes.sort(key=lambda x: x["span_count"], reverse=True)
    edges.sort(key=lambda x: x["count"], reverse=True)
    return VisualizerServiceGraphResponse(nodes=nodes, edges=edges)


@router.post("/graphs/spans", response_model=VisualizerSpanGraphResponse)
async def visualizer_data_span_graph(
    trace_ids: list[str] = Body(..., embed=True, description="Tempo trace ids (hex)"),
    service_name: str | None = Query(default=None),
) -> VisualizerSpanGraphResponse:
    all_spans = []
    for tid in trace_ids:
        raw = await tempo_get_trace(tid)
        all_spans.extend(extract_spans_best_effort(tid, raw))

    if service_name:
        all_spans = [s for s in all_spans if s.service_name == service_name]

    node_ids = {s.span_id for s in all_spans}
    nodes = [
        {
            "id": s.span_id,
            "span_id": s.span_id,
            "parent_span_id": s.parent_span_id,
            "name": s.name,
            "service_name": s.service_name,
            "trace_id": s.trace_id,
            "start_time_unix_nano": s.start_time_unix_nano,
            "end_time_unix_nano": s.end_time_unix_nano,
        }
        for s in all_spans
    ]
    edges = []
    for s in all_spans:
        if not s.parent_span_id:
            continue
        if s.parent_span_id not in node_ids:
            continue
        edges.append({"id": f"{s.parent_span_id}→{s.span_id}", "source": s.parent_span_id, "target": s.span_id})

    return VisualizerSpanGraphResponse(nodes=nodes, edges=edges)


