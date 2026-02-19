from __future__ import annotations

import json
from typing import Any, cast, override
from urllib.parse import urlparse

import websockets
from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.microrpc.duplex import DuplexMux
from rocq_doc_manager.rocq_cursor_websocket import (
    CursorDispatcher,
)
from rocq_doc_manager.rocq_cursor_websocket import (
    decoder as rdm_decoder,
)
from rocq_doc_manager.rocq_cursor_websocket import (
    encoder as rdm_encoder,
)
from rocq_pipeline.agent.base import Agent, TaskResult
from websockets.exceptions import ConnectionClosed

from .config import RemoteProofAgentConfig

logger = get_logger(__name__)

PROTOCOL_VERSION: int = 3


class RemoteAgent(Agent):
    """Agent wrapper that runs a server-side agent.

    This agent fits into rocq-pipeline like any other proof agent, but
    delegates the proof search/LLM/tool logic to a remote server.

    The remote server interacts with Rocq via JSON-RPC requests; this agent
    answers those requests by forwarding them to the *provided* local
    `RocqCursor` / rocq-doc-manager session.
    """

    def __init__(self, config: RemoteProofAgentConfig) -> None:
        super().__init__()
        self._config = config

        if not self._config.inference:
            raise ValueError(
                "RemoteProofAgent Error: 'inference' configuration is missing. "
                "The agent cannot authenticate with the backend."
            )

        api_key = self._config.inference.get("api_key")
        if not api_key:
            # We can make a helpful error message here
            provider = self._config.inference.get("provider", "unknown")
            raise ValueError(
                "RemoteProofAgent Error: No API Key found for provider "
                f"'{provider}'.\n"
                "Please ensure you have set the required environment variable "
                "(e.g. OPENROUTER_API_KEY) before running."
            )

    @classmethod
    def config_type(cls) -> type[RemoteProofAgentConfig]:
        return RemoteProofAgentConfig

    @override
    async def run(self, rc: RocqCursor) -> TaskResult:
        ws_headers = {}
        if self._config.inference:
            # Provider (e.g. "openrouter", "openai")
            if "provider" in self._config.inference:
                ws_headers["X-LLM-Provider"] = str(self._config.inference["provider"])

            # API Key (The Secret)
            if "api_key" in self._config.inference:
                ws_headers["X-LLM-Api-Key"] = str(self._config.inference["api_key"])

        # GitHub auth (server access control). We send this on both session
        # creation and websocket connection so the server can enforce
        # either/both paths.
        session_headers: dict[str, str] = {}
        if self._config.github_token:
            session_headers["Authorization"] = f"Bearer {self._config.github_token}"
            ws_headers.setdefault(
                "Authorization",
                session_headers["Authorization"],
            )

        base = self._config.server.rstrip("/")
        parsed = urlparse(base)
        scheme = "wss" if parsed.scheme == "https" else "ws"
        ws_url = f"{scheme}://{parsed.netloc}/v3/ws"

        if (
            ws_url.startswith("ws://")
            and "localhost" not in ws_url
            and "127.0.0.1" not in ws_url
        ):
            ws_url = ws_url.replace("ws://", "wss://", 1)

        logger.info(
            "remote session created",
            ws_url=ws_url,
            remote_agent=self._config.remote_agent,
        )

        async with websockets.connect(
            ws_url,
            ping_interval=self._config.ping_interval_s,
            ping_timeout=self._config.ping_timeout_s,
            additional_headers=ws_headers,
        ) as ws:

            class _WebsocketsConn:
                def __init__(self, inner: Any) -> None:
                    self._inner = inner

                async def send(self, message: str | bytes) -> None:
                    await self._inner.send(message)

                async def recv(self, decode: Any = False) -> bytes:
                    raw = await self._inner.recv()
                    if isinstance(raw, bytes):
                        return raw
                    return str(raw).encode("utf-8")

                async def close(self) -> None:
                    await self._inner.close()

            # Serve `rdm/*` requests coming from the server.
            cursor_dispatcher = CursorDispatcher({0: rc})
            mux = DuplexMux(
                _WebsocketsConn(ws),
                dispatcher=cursor_dispatcher,
                encoder=rdm_encoder,
                decoder=rdm_decoder,
            )
            await mux.start()

            run_req = {
                "protocol_version": PROTOCOL_VERSION,
                "agent_name": self._config.remote_agent,
                "agent_parameters": self._config.remote_parameters,
                "budget": self._config.budget,
                "meta": {"client_version": "remote_agent_client"},
            }

            try:
                is_exc, payload = await mux.send("control/run", [run_req], {})
            except ConnectionClosed as e:
                return await self.give_up(
                    rc,
                    message=f"websocket closed: {e.code}: {e.reason}",
                )
            finally:
                await mux.stop()

            if is_exc:
                # payload is a JSON string encoded by the shared encoder
                return await self.give_up(rc, message=f"remote exception: {payload}")

            try:
                obj = json.loads(cast(str, payload))
            except Exception:
                obj = {"summary": None}

            return await self.finished(
                rc,
                message="remote agent finished",
                side_effects={"remote_summary": obj.get("summary")},
            )
