from __future__ import annotations

import json
import re
from typing import Any

from backend.models import GraphData, GraphEdge, GraphNode, LogEntry


class Graph:
    def __init__(self) -> None:
        self.nodes: dict[str, GraphNode] = {}
        self.edges: list[GraphEdge] = []
        self.information: dict[str, Any] = {}
        self.node_counter = 1
        self.edge_counter = 1

    def add_or_create(self, node_id: str) -> GraphNode:
        node = self.nodes.get(node_id)
        if node is None:
            node = GraphNode(id=node_id, index=self.node_counter)
            self.node_counter += 1
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
                source=before.id,
                target=after.id,
                label=label,
                information=information,
                index=self.edge_counter,
            )
        )
        self.edge_counter += 1

    def to_model(self) -> GraphData:
        return GraphData(
            nodes=list(self.nodes.values()),
            edges=self.edges,
            information=self.information,
        )

    def to_dict(self) -> dict[str, Any]:
        return self.to_model().model_dump()

    def update_graph_information(self, information: dict[str, Any]) -> None:
        self.information.update(information)

    def extract_graph_info(self, log: LogEntry, labels: list[str]) -> dict[str, Any]:
        for label in labels:
            value = log.labels.get(label, None)
            if value:
                self.information[label] = value
        return self.information


def _maybe_json(value: Any) -> Any:
    if value is None or not isinstance(value, str):
        return value
    try:
        return json.loads(value)
    except json.JSONDecodeError:
        return value


def _extract_proof_Script(edges: list[GraphEdge]) -> str:
    proof_script = ""
    ptrn = re.compile(r"^insert_command\((.*)\)$", re.DOTALL)
    for edge in edges:
        status = edge.information.get("error", None)
        match = ptrn.match(edge.label)
        if match:
            tactic = match.group(1)
            if status:
                proof_script += f"(* {tactic} *) (* Failed *)\n"
            else:
                proof_script += f"{tactic}\n"

    return proof_script


def build_rocq_cursor_graph(logs: list[LogEntry]) -> Graph:
    ptrn = re.compile(r"^RocqCursor\.(.+)$")
    graph = Graph()

    for log in logs:
        message = log.labels.get("message", "NoMessage")
        match = ptrn.match(message)
        if not match:
            # this is for the idea on how we can define the key's and values which will be extarcted
            # Right now only the task_status is granteed to be extracted as it is being done in task_runner
            graph.extract_graph_info(log, ["cpp_spec", "cpp_code", "task_status"])
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
                if isinstance(error, str):
                    if error.lower() == "true":
                        error = True
                    elif error.lower() == "false":
                        error = False
                info["error"] = error
            if not error:
                # so that only proof state information is added to the node
                graph.add_information(after, info)

            args = log.labels.get("args", None)
            label = f"{cmd}({args})" if args else f"{cmd}()"
            graph.add_edge(before, after, label=label, information=info)

    # Finding the Task Status By seeing the result and proof state
    last_node = list(graph.nodes.values())[-1]
    result = last_node.information.get("result", None)
    if result is None:
        graph.update_graph_information({"taskStatus": False})
    else:
        # Default to "NoProofState" string if key is missing to distinguish from explicit None/null value
        proof_state = result.get("proof_state", "NoProofState")
        if proof_state == "NoProofState":
            graph.update_graph_information({"taskStatus": False})
        elif proof_state is None:  # proof_state = null means no goals are left to prove
            graph.update_graph_information({"taskStatus": True})
        else:
            graph.update_graph_information({"taskStatus": False})

    proof_script = _extract_proof_Script(graph.edges)
    graph.update_graph_information({"proofScript": proof_script})

    return graph
