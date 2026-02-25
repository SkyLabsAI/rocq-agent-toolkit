from __future__ import annotations

import asyncio
import json
from typing import Any, cast

import pytest


def test_remote_agent_init_requires_inference() -> None:
    from rocq_remote_agent import RemoteAgent, RemoteProofAgentConfig

    with pytest.raises(ValueError, match="inference"):
        RemoteAgent(RemoteProofAgentConfig(inference=None))


def test_remote_agent_init_requires_api_key() -> None:
    from rocq_remote_agent import RemoteAgent, RemoteProofAgentConfig

    with pytest.raises(ValueError, match="No API Key"):
        RemoteAgent(RemoteProofAgentConfig(inference={"provider": "openrouter"}))


def test_run_builds_ws_url_and_headers_and_sends_control_run(
    monkeypatch: pytest.MonkeyPatch,
    dummy_ws: Any,
) -> None:
    import rocq_remote_agent.agent as agent_mod
    from rocq_doc_manager import RocqCursor
    from rocq_remote_agent import RemoteAgent, RemoteProofAgentConfig

    captured: dict[str, Any] = {}

    class DummyConnect:
        def __init__(self, url: str, **kw: Any) -> None:
            captured["ws_url"] = url
            captured["connect_kwargs"] = kw

        async def __aenter__(self) -> Any:
            return dummy_ws

        async def __aexit__(self, _exc_type: Any, _exc: Any, _tb: Any) -> None:
            return None

    class DummyMux:
        def __init__(
            self, _conn: Any, *, dispatcher: Any, encoder: Any, decoder: Any
        ) -> None:
            captured["mux_dispatcher"] = dispatcher
            captured["mux_encoder"] = encoder
            captured["mux_decoder"] = decoder

        async def start(self) -> None:
            captured["mux_started"] = True

        async def stop(self) -> None:
            captured["mux_stopped"] = True

        async def send(
            self, method: str, args: list[Any], kwargs: dict[str, Any]
        ) -> tuple[bool, str]:
            captured["send_method"] = method
            captured["send_args"] = args
            captured["send_kwargs"] = kwargs
            return False, json.dumps(
                {
                    "success": False,
                    "summary": {"ok": True},
                    "message": "Agent made partial progress.",
                }
            )

    monkeypatch.setattr(
        agent_mod.websockets, "connect", lambda url, **kw: DummyConnect(url, **kw)
    )
    monkeypatch.setattr(agent_mod, "DuplexMux", DummyMux)

    async def _finished(
        _self: Any, _rc: Any, *, message: str, side_effects: Any = None, **_kw: Any
    ) -> Any:
        return {"message": message, "side_effects": side_effects}

    monkeypatch.setattr(RemoteAgent, "finished", _finished, raising=True)

    cfg = RemoteProofAgentConfig(
        server="http://example.com:8001",
        remote_agent="react-code-proof-agent",
        remote_parameters={"x": 1},
        inference={"provider": "openrouter", "api_key": "k"},
        github_token="gh",
    )
    agent = RemoteAgent(cfg)

    rc = cast(RocqCursor, object())
    out = asyncio.run(agent.run(rc))

    # Non-local ws:// is forced to wss:// for safety.
    assert captured["ws_url"] == "wss://example.com:8001/v3/ws"

    headers = captured["connect_kwargs"]["additional_headers"]
    assert headers["X-LLM-Provider"] == "openrouter"
    assert headers["X-LLM-Api-Key"] == "k"
    assert headers["Authorization"] == "Bearer gh"

    assert captured["send_method"] == "control/run"
    run_req = captured["send_args"][0]
    assert run_req["agent_name"] == "react-code-proof-agent"
    assert run_req["agent_parameters"] == {"x": 1}
    assert run_req["protocol_version"] == agent_mod.PROTOCOL_VERSION

    assert not out.success
    assert out.message == "Agent made partial progress."
    assert out.side_effects["remote_summary"] == {"ok": True}


def test_run_returns_give_up_on_remote_exception(
    monkeypatch: pytest.MonkeyPatch,
    dummy_ws: Any,
) -> None:
    import rocq_remote_agent.agent as agent_mod
    from rocq_doc_manager import RocqCursor
    from rocq_remote_agent import RemoteAgent, RemoteProofAgentConfig

    class DummyConnect:
        async def __aenter__(self) -> Any:
            return dummy_ws

        async def __aexit__(self, _exc_type: Any, _exc: Any, _tb: Any) -> None:
            return None

    class DummyMux:
        def __init__(
            self, _conn: Any, *, dispatcher: Any, encoder: Any, decoder: Any
        ) -> None:
            return None

        async def start(self) -> None:
            return None

        async def stop(self) -> None:
            return None

        async def send(
            self, _method: str, _args: list[Any], _kwargs: dict[str, Any]
        ) -> tuple[bool, str]:
            return True, "boom"

    monkeypatch.setattr(
        agent_mod.websockets, "connect", lambda *_a, **_kw: DummyConnect()
    )
    monkeypatch.setattr(agent_mod, "DuplexMux", DummyMux)

    async def _give_up(_self: Any, _rc: Any, *, message: str, **_kw: Any) -> Any:
        return {"message": message}

    monkeypatch.setattr(RemoteAgent, "give_up", _give_up, raising=True)

    cfg = RemoteProofAgentConfig(
        server="http://localhost:8001",
        remote_agent="react-code-proof-agent",
        inference={"provider": "openrouter", "api_key": "k"},
    )
    agent = RemoteAgent(cfg)
    out = cast(Any, asyncio.run(agent.run(cast(RocqCursor, object()))))
    assert "remote exception" in out["message"]
