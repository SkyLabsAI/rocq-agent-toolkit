# get loki logs based on run_id and task_id

from __future__ import annotations

import json
import re
from typing import Any

from backend.models import GraphData, GraphEdge, GraphNode, LogEntry


class Graph:
    def __init__(self) -> None:
        self.nodes: dict[str, GraphNode] = {}
        self.edges: list[GraphEdge] = []

    def add_or_create(self, node_id: str) -> GraphNode:
        node = self.nodes.get(node_id)
        if node is None:
            node = GraphNode(id=node_id)
            self.nodes[node_id] = node
        return node

    def add_information(self, node: GraphNode, info: dict[str, Any]) -> None:
        if info:
            node.information.update(info)

    def add_edge(
        self,
        before: GraphNode,
        after: GraphNode,
        *,
        label: str,
        information: dict[str, Any],
    ) -> None:
        self.edges.append(
            GraphEdge(
                source=before.id, target=after.id, label=label, information=information
            )
        )

    def to_model(self) -> GraphData:
        return GraphData(nodes=list(self.nodes.values()), edges=self.edges)

    def to_dict(self) -> dict[str, Any]:
        return self.to_model().model_dump()


def _maybe_json(value: Any) -> Any:
    if value is None or not isinstance(value, str):
        return value
    try:
        return json.loads(value)
    except json.JSONDecodeError:
        return value


def build_rocq_cursor_graph(logs: list[LogEntry]) -> Graph:
    ptrn = re.compile(r"^RocqCursor\.(.+)$")
    graph = Graph()

    for log in logs:
        message = log.labels.get("message", "NoMessage")
        match = ptrn.match(message)
        if not match:
            continue

        before_id = log.labels.get("before_id", None)
        if not before_id:
            continue

        cmd = match.group(1)
        before = graph.add_or_create(before_id)
        after_id = log.labels.get("after_id", None)
        if after_id:
            after = graph.add_or_create(after_id)
            info: dict[str, Any] = {}
            result = log.labels.get("result", None)
            if result is not None:
                info["result"] = _maybe_json(result)
            error = log.labels.get("error", None)
            if error is not None:
                info["error"] = error
            graph.add_information(after, info)

            args = log.labels.get("args", None)
            label = f"{cmd}({args})" if args else f"{cmd}()"
            graph.add_edge(before, after, label=label, information=info)

    return graph
