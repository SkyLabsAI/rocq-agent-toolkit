from __future__ import annotations

import asyncio
import json
from typing import Any, cast, override
from urllib.parse import urlparse

import httpx
import websockets
from brick_agents.registry import register_agent
from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_pipeline.agent.base import ProofAgent
from rocq_pipeline.agent.base.dataclasses import TaskResult
from websockets.exceptions import ConnectionClosed

from .config import RemoteProofAgentConfig

logger = get_logger(__name__)

PROTOCOL_VERSION: int = 1


def _to_jsonable(x: object) -> object:
    if hasattr(x, "to_dict") and callable(x.to_dict):
        return cast(Any, x).to_dict()
    if hasattr(x, "to_json") and callable(x.to_json):
        return cast(Any, x).to_json()
    if isinstance(x, list):
        return [_to_jsonable(v) for v in x]
    if isinstance(x, dict):
        out: dict[str, object] = {}
        for k, v in x.items():
            out[str(k)] = _to_jsonable(v)
        return out
    return x


@register_agent(script_name="remote-proof-agent")
class RemoteProofAgent(ProofAgent):
    """ProofAgent wrapper that runs a server-side agent.

    This agent fits into rocq-pipeline like any other proof agent, but
    delegates the proof search/LLM/tool logic to a remote server.

    The remote server interacts with Rocq via JSON-RPC requests; this agent
    answers those requests by forwarding them to the *provided* local
    `RocqCursor` / rocq-doc-manager session.
    """

    def __init__(self, config: RemoteProofAgentConfig) -> None:
        super().__init__()
        self._config = config

    @classmethod
    def config_type(cls) -> type[RemoteProofAgentConfig]:
        return RemoteProofAgentConfig

    @override
    async def prove(self, rc: RocqCursor) -> TaskResult:
        base = self._config.server.rstrip("/")
        async with httpx.AsyncClient() as client:
            session = await client.post(f"{base}/v1/session")
            session.raise_for_status()
            sess_data = session.json()
        token = cast(str, sess_data["token"])
        ws_url: str
        if "ws_url" in sess_data:
            ws_url = cast(str, sess_data["ws_url"])
        else:
            ws_path = cast(str, sess_data["ws_path"])
            parsed = urlparse(base)
            scheme = "wss" if parsed.scheme == "https" else "ws"
            ws_url = f"{scheme}://{parsed.netloc}{ws_path}"

        logger.info(
            "remote session created",
            ws_url=ws_url,
            remote_agent=self._config.remote_agent,
        )

        def _handle_request(
            *,
            req_id: int,
            method: str,
            params: list[object],
        ) -> dict[str, object]:
            if method == "quit":
                return {"jsonrpc": "2.0", "id": req_id, "result": None}

            fn = getattr(api, method, None)
            if not callable(fn):
                return {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32601, "message": f"method not found: {method}"},
                }

            try:
                result = fn(*params)
                if isinstance(result, rdm_api.Err):
                    return {
                        "jsonrpc": "2.0",
                        "id": req_id,
                        "error": {
                            "code": -32803,
                            "message": result.message,
                            "data": _to_jsonable(result.data),
                        },
                    }
                return {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": _to_jsonable(result),
                }
            except Exception as e:
                return {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32000, "message": str(e)},
                }

        async with websockets.connect(
            ws_url,
            ping_interval=self._config.ping_interval_s,
            ping_timeout=self._config.ping_timeout_s,
        ) as ws:
            hello = {
                "type": "hello",
                "protocol_version": PROTOCOL_VERSION,
                "token": token,
                "agent": {
                    "name": self._config.remote_agent,
                    "parameters": self._config.remote_parameters,
                    "inference": self._config.inference,
                    "budget": self._config.budget,
                },
                "locator": {"kind": "current_goal"},
                "meta": {"client_version": "brick-agents/remote-proof-agent"},
            }
            await ws.send(json.dumps(hello))

            hello_ack = False

            while True:
                try:
                    raw = await ws.recv()
                except ConnectionClosed as e:
                    return self.give_up(
                        rc,
                        message=f"websocket closed: {e.code}: {e.reason}",
                    )

                try:
                    obj = json.loads(raw if isinstance(raw, str) else raw.decode("utf-8"))
                except Exception:
                    continue

                if not isinstance(obj, dict) or not all(
                    isinstance(k, str) for k in obj.keys()
                ):
                    continue

                # JSON-RPC request from server (forward to local RDM API).
                if obj.get("jsonrpc") == "2.0" and "id" in obj and "method" in obj:
                    if not hello_ack:
                        continue
                    req_id = obj.get("id")
                    method = obj.get("method")
                    params = obj.get("params")
                    if not isinstance(req_id, int) or not isinstance(method, str):
                        continue
                    if not isinstance(params, list):
                        params = []

                    resp = await asyncio.to_thread(
                        _handle_request,
                        req_id=req_id,
                        method=method,
                        params=cast(list[object], params),
                    )
                    await ws.send(json.dumps(resp))
                    continue

                if obj.get("type") == "event":
                    ev = obj
                    logger.info(
                        "remote event",
                        event_level=str(ev.get("level", "info")),
                        event_message=str(ev.get("message", "")),
                        data=cast(object, ev.get("data")),
                    )
                    continue

                if obj.get("type") == "hello_ack":
                    hello_ack = True
                    continue

                if obj.get("type") == "result":
                    # The remote agent has already driven RDM operations via our
                    # JSON-RPC forwarding, so `rc` reflects the proof progress.
                    await ws.close()
                    return self.finished(
                        rc,
                        message=f"remote agent finished: {obj.get('agent_name')}",
                        side_effects={"remote_summary": obj.get("summary")},
                    )

                if obj.get("type") == "error":
                    await ws.close()
                    return self.give_up(
                        rc,
                        message=(
                            f"remote error: {obj.get('code')}: {obj.get('message')}"
                        ),
                        side_effects={"remote_error": obj.get("data")},
                    )
