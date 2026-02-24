from __future__ import annotations

from pathlib import Path

import pytest


def test_cached_token_roundtrip(tmp_path: Path) -> None:
    from rocq_remote_agent.github_auth import _read_cached_token, _write_cached_token

    p = tmp_path / "github_token.json"
    _write_cached_token(p, "tok123")
    assert _read_cached_token(p) == "tok123"


def test_resolve_github_token_prefers_env(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from rocq_remote_agent.github_auth import _write_cached_token, resolve_github_token

    cache = tmp_path / "github_token.json"
    _write_cached_token(cache, "tok-from-cache")

    monkeypatch.setenv("GH_TOKEN", "tok-from-env")
    tok = resolve_github_token(
        token_env_names=["GH_TOKEN", "GITHUB_TOKEN"], cache_path=cache
    )
    assert tok == "tok-from-env"


def test_resolve_github_token_uses_cache_when_env_missing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from rocq_remote_agent.github_auth import _write_cached_token, resolve_github_token

    monkeypatch.delenv("GH_TOKEN", raising=False)
    monkeypatch.delenv("GITHUB_TOKEN", raising=False)

    cache = tmp_path / "github_token.json"
    _write_cached_token(cache, "tok-from-cache")

    tok = resolve_github_token(
        token_env_names=["GH_TOKEN", "GITHUB_TOKEN"], cache_path=cache
    )
    assert tok == "tok-from-cache"
