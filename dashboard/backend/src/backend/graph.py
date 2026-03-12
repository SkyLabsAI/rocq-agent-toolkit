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


def _extract_tactic_lists(edges: list[GraphEdge]) -> str:
    tactic_lists = ""
    insert_ptrn = re.compile(r"^insert_command\((.*)\)$", re.DOTALL)
    revert_ptrn = re.compile(r"^revert_before\((.*)\)$", re.DOTALL)
    for edge in edges:
        status = edge.information.get("error", None)
        insert_match = insert_ptrn.match(edge.label)
        if insert_match:
            tactic = insert_match.group(1)
            if status:
                tactic_lists += f"(* {tactic} *) (* Failed *)\n"
            else:
                tactic_lists += f"{tactic}\n"
            continue

        # `revert_before` is not a Rocq command; include it as a comment for traceability.
        revert_match = revert_ptrn.match(edge.label)
        if revert_match:
            delta = revert_match.group(1)
            tactic_lists += f"(* revert_before({delta}) *)\n"

    return tactic_lists


def _extract_proof_script(edges: list[GraphEdge]) -> str:
    insert_ptrn = re.compile(r"^insert_command\((.*)\)$", re.DOTALL)
    revert_ptrn = re.compile(r"^revert_before\((.*)\)$", re.DOTALL)
    # Stack of successful commands paired with the node reached after applying them.
    active_tactics: list[tuple[str, str]] = []

    for edge in sorted(edges, key=lambda item: item.index):
        insert_match = insert_ptrn.match(edge.label)
        if insert_match:
            if edge.information.get("error", False):
                continue
            active_tactics.append((edge.target, insert_match.group(1)))
            continue

        if not revert_ptrn.match(edge.label):
            continue

        revert_target = edge.target
        while active_tactics and active_tactics[-1][0] != revert_target:
            active_tactics.pop()

    if not active_tactics:
        return ""

    return "".join(f"{tactic}\n" for _, tactic in active_tactics)


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

        before_id = log.labels.get("before.id") or log.labels.get("before_id")
        if not before_id:
            continue

        cmd = match.group(1)
        before = graph.add_or_create(before_id)
        after_id = log.labels.get("after.id") or log.labels.get("after_id")
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

            raw_args = _maybe_json(log.labels.get("args", None))
            if raw_args is None and log.line:
                try:
                    raw_args = json.loads(log.line).get("args", None)
                except (json.JSONDecodeError, AttributeError):
                    pass

            if cmd == "insert_command":
                if isinstance(raw_args, list) and raw_args:
                    args: Any = raw_args[0]
                else:
                    args = raw_args
            # For revert_before: new format has no top-level delta (use args["index"]);
            # old format had a top-level delta field.
            elif cmd == "revert_before":
                delta = log.labels.get("delta", None)
                if delta is not None:
                    args = delta
                elif isinstance(raw_args, dict) and "index" in raw_args:
                    args = raw_args["index"]
                else:
                    args = raw_args
            else:
                args = raw_args
            label = f"{cmd}({args})" if args is not None else f"{cmd}()"
            graph.add_edge(before, after, label=label, information=info)

    tactic_lists = _extract_tactic_lists(graph.edges)
    proof_script = _extract_proof_script(graph.edges)
    graph.update_graph_information(
        {
            "tactic_lists": tactic_lists,
            "proofScript": proof_script,
        }
    )

    return graph
