from __future__ import annotations

import argparse
import asyncio
import json
from pathlib import Path
from typing import cast
from urllib.parse import urlparse

import httpx
import websockets
from rocq_doc_manager import DuneUtil
from websockets.exceptions import ConnectionClosed

from remote_agent_client.protocol import (
    AgentConfig,
    BudgetConfig,
    InferenceConfig,
    JsonValue,
    LocatorConfig,
    ProxyHello,
    ProxyMeta,
)

_TP_PREFIX = b"Content-Length: "


def _find_dune_root(file_path: Path) -> Path | None:
    """Find the closest parent directory that looks like a dune workspace."""
    for d in [file_path.parent, *file_path.parents]:
        if (d / "dune-project").exists() or (d / "dune-workspace").exists():
            return d
    return None


class JsonRpcTpProcess:
    """Minimal Content-Length framed transport to rocq-doc-manager subprocess."""

    def __init__(self, proc: asyncio.subprocess.Process):
        self._proc = proc
        assert proc.stdin is not None
        assert proc.stdout is not None
        self._stdin: asyncio.StreamWriter = proc.stdin
        self._stdout: asyncio.StreamReader = proc.stdout

    async def send(self, msg: dict[str, JsonValue]) -> None:
        data = json.dumps(msg).encode("utf-8")
        header = _TP_PREFIX + str(len(data) + 1).encode("ascii") + b"\r\n\r\n"
        self._stdin.write(header)
        self._stdin.write(data)
        self._stdin.write(b"\n")
        await self._stdin.drain()

    async def recv(self) -> dict[str, JsonValue]:
        header = await self._stdout.readline()
        if not header.startswith(_TP_PREFIX):
            raise RuntimeError(f"rdm invalid header: {header!r}")
        n = int(header[len(_TP_PREFIX) :].strip().rstrip(b"\r"))
        _ = await self._stdout.readline()
        raw = await self._stdout.readexactly(n)
        return cast(dict[str, JsonValue], json.loads(raw.decode("utf-8")))


def _parse_kv_json(raw: str) -> tuple[str, JsonValue]:
    if "=" not in raw:
        raise ValueError("expected KEY=JSON")
    k, v = raw.split("=", 1)
    return k.strip(), cast(JsonValue, json.loads(v))


async def run_proxy(
    *,
    ws_url: str,
    token: str,
    file_path: str,
    agent_name: str,
    agent_params: dict[str, JsonValue],
    inference: InferenceConfig | None,
    budget: BudgetConfig,
    locator: LocatorConfig,
) -> None:
    file_path = str(Path(file_path).resolve())
    print(f"[proxy] file={file_path}", flush=True)

    print("[proxy] computing rocq args ...", flush=True)
    fp = Path(file_path)
    dune_root = _find_dune_root(fp)
    try:
        if dune_root is None:
            print(
                "[proxy] no dune-project/dune-workspace found; using rocq_args=[]",
                flush=True,
            )
            rocq_args = []
        else:
            rel = fp.relative_to(dune_root)
            rocq_args = DuneUtil.rocq_args_for(rel, cwd=dune_root)
    except (FileNotFoundError, DuneUtil.NotFound) as e:
        print(f"[proxy] dune args unavailable ({e}); using rocq_args=[]", flush=True)
        rocq_args = []
    # print(f"[proxy] rocq args: {rocq_args}", flush=True)

    cmd = [
        "dune",
        "exec",
        "--no-build",
        "--no-print-directory",
        "--display=quiet",
        "rocq-doc-manager",
        "--",
        file_path,
        "--",
        *rocq_args,
    ]
    print(
        f"[proxy] starting rocq-doc-manager: {' '.join(cmd)}",
        flush=True,
    )
    proc: asyncio.subprocess.Process | None = None
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        tp = JsonRpcTpProcess(proc)

        # Drain initial ready message.
        _ = await tp.recv()
        print("[proxy] rocq-doc-manager ready", flush=True)

        print(f"[proxy] connecting ws: {ws_url}", flush=True)
        async with websockets.connect(ws_url, ping_interval=20, ping_timeout=20) as ws:
            hello = ProxyHello(
                token=token,
                agent=AgentConfig(
                    name=agent_name,
                    parameters=agent_params,
                    inference=inference,
                    budget=budget,
                ),
                locator=locator,
                meta=ProxyMeta(
                    file_path=file_path,
                    rocq_args=rocq_args,
                    client_version="rocq-agent-proxy/1",
                ),
            )
            # Use JSON mode so SecretStr (BYOK) is serialized as a string.
            await ws.send(json.dumps(hello.model_dump(mode="json")))
            print("[proxy] sent hello", flush=True)

            while True:
                try:
                    raw = await ws.recv()
                except ConnectionClosed as e:
                    print(
                        f"[proxy] websocket closed ({e.code}): {e.reason}",
                        flush=True,
                    )
                    break

                if isinstance(raw, bytes):
                    raw = raw.decode("utf-8")
                msg = cast(JsonValue, json.loads(raw))
                if isinstance(msg, dict) and msg.get("type") == "event":
                    print(
                        f"[server] {msg.get('level', 'info')}: {msg.get('message')}",
                        flush=True,
                    )
                    continue
                if isinstance(msg, dict) and msg.get("type") == "hello_ack":
                    print(f"[proxy] session={msg.get('session_id')} ready", flush=True)
                    continue
                if isinstance(msg, dict) and msg.get("type") == "error":
                    print(
                        f"[server] error: {msg.get('code')}: {msg.get('message')}",
                        flush=True,
                    )
                    break
                if isinstance(msg, dict) and msg.get("type") == "result":
                    print(
                        f"[proxy] server result agent={msg.get('agent_name')}",
                        flush=True,
                    )
                    proof = msg.get("proof", [])
                    if isinstance(proof, list):
                        for line in proof:
                            print(f"  {line}", flush=True)
                    break

                # Default: assume JSON-RPC request; forward to local rocq-doc-manager.
                req = cast(dict[str, JsonValue], msg)
                await tp.send(req)
                resp = await tp.recv()
                await ws.send(json.dumps(resp))
    finally:
        if proc is not None:
            try:
                if proc.stdin is not None:
                    proc.stdin.close()
            except Exception:
                pass
            try:
                if proc.returncode is None:
                    proc.terminate()
            except ProcessLookupError:
                pass
            try:
                await asyncio.wait_for(proc.wait(), timeout=5.0)
            except TimeoutError:
                try:
                    proc.kill()
                except ProcessLookupError:
                    pass
                await proc.wait()


def _parse() -> argparse.Namespace:
    p = argparse.ArgumentParser("rocq-remote-rdm-proxy")
    p.add_argument(
        "--ws-url",
        type=str,
        help="wss://... websocket url",
        required=False,
    )
    p.add_argument("--token", type=str, required=False)
    p.add_argument("--file", type=str, required=True)
    p.add_argument(
        "--server",
        type=str,
        required=False,
        help="https://host:port base url; creates a session",
    )

    p.add_argument(
        "--agent",
        type=str,
        required=True,
        help="Agent name (e.g. react-code-proof-agent)",
    )
    p.add_argument(
        "--agent-param",
        action="append",
        default=[],
        help="KEY=JSON (repeatable)",
    )

    p.add_argument("--provider", type=str, required=False)
    p.add_argument("--model", type=str, required=False)
    p.add_argument("--api-key", type=str, required=False)
    p.add_argument("--base-url", type=str, required=False)

    p.add_argument("--max-wall-seconds", type=int, required=False)
    p.add_argument("--max-llm-calls", type=int, required=False)
    p.add_argument("--max-tool-calls", type=int, required=False)

    p.add_argument(
        "--locator",
        type=str,
        default="admit",
        help="Currently only 'admit' is supported",
    )
    return p.parse_args()


def main() -> None:
    args = _parse()
    ws_url = args.ws_url
    token = args.token

    if (ws_url is None or token is None) and args.server:
        base = args.server.rstrip("/")
        resp = httpx.post(f"{base}/v1/session")
        resp.raise_for_status()
        data = resp.json()
        ws_path = data.get("ws_path")
        if ws_path:
            parsed = urlparse(base)
            scheme = "wss" if parsed.scheme == "https" else "ws"
            ws_url = f"{scheme}://{parsed.netloc}{ws_path}"
        else:
            ws_url = data["ws_url"]
        token = data["token"]
        print(f"[proxy] created session: ws_url={ws_url}", flush=True)

    if ws_url is None or token is None:
        raise SystemExit("need either --ws-url + --token, or --server")

    agent_params: dict[str, JsonValue] = {}
    for item in args.agent_param:
        k, v = _parse_kv_json(item)
        agent_params[k] = v

    inf: InferenceConfig | None = None
    if args.provider or args.model or args.api_key or args.base_url:
        inf = InferenceConfig(
            provider=args.provider,
            model=args.model,
            base_url=args.base_url,
            api_key=None if args.api_key is None else args.api_key,
        )

    budget = BudgetConfig(
        max_wall_seconds=args.max_wall_seconds,
        max_llm_calls=args.max_llm_calls,
        max_tool_calls=args.max_tool_calls,
    )
    if args.locator != "admit":
        raise SystemExit("only --locator=admit is supported right now")
    locator = LocatorConfig(kind="admit")

    asyncio.run(
        run_proxy(
            ws_url=ws_url,
            token=token,
            file_path=args.file,
            agent_name=args.agent,
            agent_params=agent_params,
            inference=inf,
            budget=budget,
            locator=locator,
        )
    )


if __name__ == "__main__":
    main()
