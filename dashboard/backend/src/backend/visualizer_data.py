"""
Visualizer Data API

Stable API surface for the dashboard visualizer UI under:

  /visualizer/data/*
"""

from __future__ import annotations

import json
import logging
from datetime import UTC, datetime, timedelta
from typing import Any

from fastapi import APIRouter, Depends, HTTPException, Query
from sqlmodel import Session

from backend.dal import get_estimated_time_for_task_from_db, get_task_name_from_db
from backend.database import get_session
from backend.graph import build_rocq_cursor_graph
from backend.models import (
    ObservabilityGraphResponse,
    VisualizerSpanLite,
    VisualizerSpansResponse,
    VisualizerTraceIdsResponse,
)
from backend.utils import fetch_observability_logs
from backend.visualizer import (
    extract_spans_best_effort,
    loki_query_range,
    tempo_get_trace,
)

router = APIRouter(prefix="/visualizer/data", tags=["visualizer"])


logger = logging.getLogger(__name__)


@router.get("/tempo/traces/{trace_id}/spans", response_model=VisualizerSpansResponse)
async def visualizer_data_tempo_trace_spans(trace_id: str) -> VisualizerSpansResponse:
    raw = await tempo_get_trace(trace_id)
    spans = extract_spans_best_effort(trace_id, raw)
    return VisualizerSpansResponse(
        spans=[VisualizerSpanLite(**s.__dict__) for s in spans]
    )


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
    service_label: str = Query(
        default="service_name", description="Loki label key for service"
    ),
    trace_id_field: str = Query(
        default="trace_id", description="JSON field for trace id"
    ),
    span_id_field: str = Query(default="span_id", description="JSON field for span id"),
) -> dict[str, Any]:
    start = datetime.fromtimestamp(start_ms / 1000, tz=UTC)
    end = datetime.fromtimestamp(end_ms / 1000, tz=UTC)
    logql = (
        f'{{{service_label}="{service}"}} | json '
        f'| {trace_id_field}="{trace_id}" '
        f'| {span_id_field}="{span_id}"'
    )
    return await loki_query_range(
        query=logql, start=start, end=end, limit=limit, direction=direction
    )


# This endpoint can be remove after traceid is already available to the frontend
@router.get("/runs/{run_id}/trace-ids", response_model=VisualizerTraceIdsResponse)
async def visualizer_data_trace_ids_for_run(
    run_id: str,
    limit: int = Query(
        default=50, ge=1, le=500, description="Max unique trace ids to return"
    ),
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
    data = await loki_query_range(
        query=logql, start=start, end=end, limit=5000, direction="backward"
    )
    trace_ids: set[str] = set()

    for stream in data.get("data", {}).get("result", []) or []:
        for _ts_ns, line in stream.get("values", []) or []:
            try:
                obj = json.loads(line)
            except Exception:
                continue
            tid = (
                obj.get(trace_id_field) or obj.get("otelTraceID") or obj.get("trace_id")
            )
            if isinstance(tid, str) and tid:
                trace_ids.add(tid)
            if len(trace_ids) >= limit:
                break
        if len(trace_ids) >= limit:
            break

    out = sorted(trace_ids)
    return VisualizerTraceIdsResponse(run_id=run_id, trace_ids=out, total=len(out))


@router.get("/tactic/graph", response_model=ObservabilityGraphResponse)
async def get_tactic_graph(
    run_id: str = Query(..., description="Run ID to fetch logs for"),
    task_id: int = Query(..., description="Database task ID to fetch logs for"),
    session: Session = Depends(get_session),  # noqa: B008
) -> ObservabilityGraphResponse:
    """
    Build a RocqCursor graph from tactics for a specific run and task.
    """
    try:
        task_name = get_task_name_from_db(session, task_id)
        if task_name is None:
            raise HTTPException(
                status_code=404, detail=f"Task with ID {task_id} not found"
            )

        estimated_time = get_estimated_time_for_task_from_db(session, run_id, task_id)

        if not estimated_time:
            raise HTTPException(
                status_code=404,
                detail=f"No run data found for run_id='{run_id}' and task_id={task_id}",
            )

        logs = await fetch_observability_logs(
            run_id=run_id, task_name=task_name, estimated_time=estimated_time
        )

        if not logs:
            raise HTTPException(
                status_code=404,
                detail=f"No logs found for run_id='{run_id}' and task_id={task_id}",
            )

        graph = build_rocq_cursor_graph(logs)
        graph_payload = graph.to_model()

        logger.info(
            "Built RocqCursor graph: nodes=%d edges=%d",
            len(graph.nodes),
            len(graph.edges),
        )

        return ObservabilityGraphResponse(
            run_id=run_id,
            task_id=task_id,
            task_name=task_name,
            graph=graph_payload,
            total_nodes=len(graph.nodes),
            total_edges=len(graph.edges),
        )
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error building observability graph: {e}", exc_info=True)
        raise HTTPException(
            status_code=500, detail=f"Error building graph: {str(e)}"
        ) from e
