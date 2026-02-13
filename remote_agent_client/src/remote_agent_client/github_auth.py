from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass
from pathlib import Path

import httpx


@dataclass(frozen=True)
class DeviceFlowInfo:
    device_code: str
    user_code: str
    verification_uri: str
    expires_in: int
    interval: int


def _default_token_cache_path() -> Path:
    # Keep this intentionally simple and cross-platform.
    # - macOS/Linux: ~/.config/...
    # - Windows: still works (home dir) and is acceptable for our usage.
    return Path.home() / ".config" / "rocq-agent-toolkit" / "github_token.json"


def _read_cached_token(path: Path) -> str | None:
    try:
        raw = path.read_text(encoding="utf-8")
        obj = json.loads(raw)
        tok = obj.get("access_token")
        if isinstance(tok, str) and tok.strip():
            return tok.strip()
    except Exception:
        return None
    return None


def _write_cached_token(path: Path, token: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "access_token": token,
        "cached_at_ms": int(time.time() * 1000),
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    try:
        os.chmod(path, 0o600)
    except Exception:
        # Best-effort; some platforms/filesystems may not support chmod.
        pass


def github_device_authorization(
    client_id: str,
    *,
    scope: str = "read:user",
) -> DeviceFlowInfo:
    with httpx.Client(timeout=30.0) as client:
        resp = client.post(
            "https://github.com/login/device/code",
            data={"client_id": client_id, "scope": scope},
            headers={"Accept": "application/json"},
        )
        resp.raise_for_status()
        data = resp.json()
    return DeviceFlowInfo(
        device_code=str(data["device_code"]),
        user_code=str(data["user_code"]),
        verification_uri=str(data["verification_uri"]),
        expires_in=int(data.get("expires_in", 900)),
        interval=int(data.get("interval", 5)),
    )


def github_device_poll_for_token(
    client_id: str,
    *,
    device_code: str,
    interval_s: int,
    expires_in_s: int,
) -> str:
    deadline = time.time() + float(expires_in_s)
    poll = max(1, int(interval_s))
    while time.time() < deadline:
        with httpx.Client(timeout=30.0) as client:
            resp = client.post(
                "https://github.com/login/oauth/access_token",
                data={
                    "client_id": client_id,
                    "device_code": device_code,
                    "grant_type": "urn:ietf:params:oauth:grant-type:device_code",
                },
                headers={"Accept": "application/json"},
            )
            resp.raise_for_status()
            data = resp.json()

        tok = data.get("access_token")
        if isinstance(tok, str) and tok:
            return tok

        err = data.get("error")
        if err == "authorization_pending":
            time.sleep(poll)
            continue
        if err == "slow_down":
            poll += 5
            time.sleep(poll)
            continue

        desc = data.get("error_description") or err or "unknown error"
        raise RuntimeError(f"GitHub OAuth device flow failed: {desc}")

    raise RuntimeError(
        "GitHub OAuth device flow timed out: user did not authorize in time"
    )


def resolve_github_token(
    *,
    token_env_names: list[str],
    cache_path: Path | None = None,
) -> str | None:
    for name in token_env_names:
        if not name:
            continue
        v = os.environ.get(name)
        if isinstance(v, str) and v.strip():
            return v.strip()
    path = cache_path or _default_token_cache_path()
    return _read_cached_token(path)


def interactive_github_login_device_flow(
    *,
    client_id: str,
    scope: str = "read:user",
    cache_path: Path | None = None,
) -> str:
    info = github_device_authorization(client_id, scope=scope)

    # Keep stdout UX minimal and copy/paste friendly.
    print()
    print("GitHub authentication required.")
    print(f"1) Open: {info.verification_uri}")
    print(f"2) Enter code: {info.user_code}")
    print("Waiting for authorization...")
    print()

    token = github_device_poll_for_token(
        client_id,
        device_code=info.device_code,
        interval_s=info.interval,
        expires_in_s=info.expires_in,
    )
    _write_cached_token(cache_path or _default_token_cache_path(), token)
    return token
