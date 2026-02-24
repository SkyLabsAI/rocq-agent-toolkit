import pytest


def test_parse_kv_json_parses_json_value() -> None:
    from rocq_remote_agent.builder import _parse_kv_json

    k, v = _parse_kv_json('foo={"a": 1}')
    assert k == "foo"
    assert v == {"a": 1}


def test_parse_kv_json_requires_equals() -> None:
    from rocq_remote_agent.builder import _parse_kv_json

    with pytest.raises(ValueError, match="expected KEY=JSON"):
        _parse_kv_json("nope")


def test_builder_requires_api_key_env(monkeypatch: pytest.MonkeyPatch) -> None:
    from rocq_remote_agent.builder import RemoteAgentBuilder

    # Ensure the default env var is missing.
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)

    b = RemoteAgentBuilder()
    with pytest.raises(ValueError, match="OPENROUTER_API_KEY"):
        b.add_args([])


def test_builder_uses_cached_or_env_github_token(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import importlib

    builder_mod = importlib.import_module("rocq_remote_agent.builder")
    from rocq_remote_agent.agent import RemoteAgent
    from rocq_remote_agent.builder import RemoteAgentBuilder

    monkeypatch.setenv("OPENROUTER_API_KEY", "ok-api-key")

    # Prefer non-interactive token resolution when available.
    monkeypatch.setattr(
        builder_mod, "resolve_github_token", lambda **_kw: "gh-from-env"
    )
    monkeypatch.setattr(
        builder_mod,
        "interactive_github_login_device_flow",
        lambda **_kw: pytest.fail("interactive login should not be called"),
    )

    b = RemoteAgentBuilder()
    b.add_args(
        [
            "--server",
            "http://example:8001",
            "--remote-agent",
            "react-code-proof-agent",
            "--remote-param",
            "x=1",
            "--remote-param",
            'obj={"k": "v"}',
            "--provider",
            "openrouter",
        ]
    )

    built = b()
    assert isinstance(built, RemoteAgent)
    assert built._config.server == "http://example:8001"
    assert built._config.remote_agent == "react-code-proof-agent"
    assert built._config.remote_parameters == {"x": 1, "obj": {"k": "v"}}
    assert built._config.inference == {
        "provider": "openrouter",
        "api_key": "ok-api-key",
    }
    assert built._config.github_token == "gh-from-env"


def test_builder_falls_back_to_device_flow(monkeypatch: pytest.MonkeyPatch) -> None:
    import importlib

    builder_mod = importlib.import_module("rocq_remote_agent.builder")
    from rocq_remote_agent.agent import RemoteAgent
    from rocq_remote_agent.builder import RemoteAgentBuilder

    monkeypatch.setenv("OPENROUTER_API_KEY", "ok-api-key")

    monkeypatch.setattr(builder_mod, "resolve_github_token", lambda **_kw: None)
    monkeypatch.setattr(
        builder_mod,
        "interactive_github_login_device_flow",
        lambda **_kw: "gh-device-flow",
    )

    b = RemoteAgentBuilder()
    b.add_args([])
    built = b()
    assert isinstance(built, RemoteAgent)
    assert built._config.github_token == "gh-device-flow"
