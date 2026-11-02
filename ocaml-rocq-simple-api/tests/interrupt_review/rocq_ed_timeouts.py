#!/usr/bin/env python3
"""Historical diagnostics for revision 654c7ffe, also a reusable helper module.

Most default failure observations were FIXED at 0200345f. Do not interpret this
legacy suite's failed observations as current regressions. Run rocq_ed_review.py
for current correct-behavior assertions. The old cases remain for historical
comparison; all sessions use temporary caches and no interposition hooks.
"""
import argparse
import ctypes
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
from run import ROOT, REL, reap_descendants

FIXTURE = REL / "rocq_ed_fixture/Probe.v"
LOOP = "Goal True. Proof. let rec loop := loop in loop."
FINITE = "Goal True. Proof. Timeout 1 let rec loop := loop in loop."


def check(value, message):
    if not value:
        raise AssertionError(message)


def wait_for(predicate, message, seconds=8):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.01)
    raise AssertionError(message)


def alive(pid):
    try:
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return fields[0] != "Z"
    except FileNotFoundError:
        return False


def cpu_ticks(pid):
    fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
    return int(fields[11]) + int(fields[12])


def children(pid):
    try:
        return list(map(int, Path(f"/proc/{pid}/task/{pid}/children").read_text().split()))
    except FileNotFoundError:
        return []


def command(cache, *args, timed=None):
    prefix = ["direnv", "exec", ".", "env", f"XDG_CACHE_HOME={cache}"]
    if timed:
        prefix += ["timeout", *timed]
    return prefix + ["rocq-ed", *args]


def last_line(text):
    plain = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", text)
    return plain.strip().splitlines()[-1]


def cli(cache, *args, timed=None):
    return subprocess.run(command(cache, *args, timed=timed), cwd=ROOT,
                          capture_output=True, text=True, timeout=15)


def session(cache):
    result = cli(cache, "init", str(FIXTURE))
    check(result.returncode == 0, f"init failed: {result.stdout}\n{result.stderr}")
    match = re.search(r"ROCQED_SESSION_ID=([^\s]+)", result.stdout)
    check(match, f"missing session ID: {result.stdout}")
    return session_info(cache, match.group(1))


def session_info(cache, session_id):
    data = Path(cache) / "rocq-ed" / session_id
    server = int((data / "pid").read_text().strip())
    private = []
    for pid in children(server):
        try:
            if b"rocq-simple-api.private.toplevel" in Path(f"/proc/{pid}/cmdline").read_bytes():
                private.append(pid)
        except FileNotFoundError:
            pass
    check(len(private) == 1, f"expected one real private toplevel, got {private}")
    top = private[0]
    print(f"server pid/pgid/sid={server}/{os.getpgid(server)}/{os.getsid(server)}; "
          f"private={top}/{os.getpgid(top)}/{os.getsid(top)}", flush=True)
    return session_id, data, server, top


def timed_client(cache, *, finite, signal_name="TERM", foreground=False):
    session_id, data, server, top = session(cache)
    options = ["--signal", signal_name, "--kill-after=0.2s"]
    if foreground:
        options += ["--foreground"]
    options += ["0.2s"]
    result = cli(cache, "insert", "-s", session_id, "--text", FINITE if finite else LOOP,
                 timed=options)
    check(result.returncode == 124, f"expected timeout=124, got {result.returncode}: {result.stderr}")
    log = (data / "log").read_text()
    check("Request [" in log and "let rec loop" in log, "timeout occurred before the daemon received insertion")
    check(alive(server) and alive(top), "daemon/private process already gone at client deadline")
    print(f"client timeout=124 ({signal_name}); server and private are still alive", flush=True)
    if finite:
        wait_for(lambda: not alive(server), "daemon did not die after replying to the disconnected client")
        _, daemon_status = os.waitpid(server, 0)
        check(os.WIFSIGNALED(daemon_status) and os.WTERMSIG(daemon_status) == signal.SIGPIPE,
              f"expected daemon SIGPIPE after lost response, got wait status {daemon_status}")
        status = cli(cache, "status", "-s", session_id)
        check(status.returncode == 123, f"expected dead-session=123, got {status.returncode}")
        print(f"after the one-second Rocq Timeout: daemon died by SIGPIPE; status={status.returncode}; "
              f"{last_line(status.stderr)}", flush=True)
        print("daemon log tail:\n" + "\n".join((data / "log").read_text().splitlines()[-4:]), flush=True)
    else:
        ticks = cpu_ticks(top)
        time.sleep(0.25)
        check(cpu_ticks(top) > ticks, "private toplevel did not continue consuming CPU")
        status = cli(cache, "status", "-s", session_id, timed=["0.2s"])
        check(status.returncode == 124, f"expected queued status to time out, got {status.returncode}")
        check(alive(server) and alive(top), "ongoing tactic was unexpectedly cancelled")
        print("infinite tactic continues consuming CPU; subsequent status also times out=124", flush=True)


def foreground_server(cache, *, signal_name):
    with tempfile.TemporaryFile(mode="w+") as output:
        process = subprocess.Popen(command(cache, "init", "--no-daemon", str(FIXTURE),
            timed=["--signal", signal_name, "--kill-after=0.2s", "3s"]), cwd=ROOT,
            stdout=output, stderr=output)
        def ready():
            output.seek(0)
            return re.search(r"ROCQED_SESSION_ID=([^\s]+)", output.read())
        wait_for(ready, "foreground server did not report readiness before timeout")
        session_id, _, server, top = session_info(cache, ready().group(1))
        writer = subprocess.Popen(command(cache, "insert", "-s", session_id, "--text", LOOP),
                                  cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        # Confirm the real tactic is spinning before the foreground server deadline.
        ticks = cpu_ticks(top)
        wait_for(lambda: cpu_ticks(top) > ticks + 5, "loop did not start before server deadline")
        code = process.wait(timeout=8)
        _, stderr = writer.communicate(timeout=3)
        check(code == 124, f"expected foreground timeout=124, got {code}")
        check(not alive(server) and alive(top), "expected dead server but surviving busy private session")
        ticks = cpu_ticks(top)
        time.sleep(0.1)
        check(cpu_ticks(top) > ticks, "orphaned private toplevel is not still computing")
        print(f"timeout of foreground server ({signal_name})=124; server dead; private still consumes CPU", flush=True)
        print(f"in-flight client exit={writer.returncode}; {last_line(stderr)}", flush=True)


def rocq_timeout_control(cache):
    session_id, _, server, top = session(cache)
    result = cli(cache, "insert", "-s", session_id, "--text", FINITE)
    check(result.returncode == 1, f"expected ordinary Rocq timeout error=1, got {result.returncode}")
    status = cli(cache, "status", "-s", session_id)
    check(status.returncode == 0 and alive(server) and alive(top), "ordinary Rocq Timeout killed the session")
    print("Rocq's own Timeout returns command error=1; session remains usable (status=0)", flush=True)


CASES = {
    "client-term-infinite": lambda cache: timed_client(cache, finite=False),
    "client-int-infinite": lambda cache: timed_client(cache, finite=False, signal_name="INT"),
    "client-foreground-infinite": lambda cache: timed_client(cache, finite=False, foreground=True),
    "client-term-finite": lambda cache: timed_client(cache, finite=True),
    "server-term-infinite": lambda cache: foreground_server(cache, signal_name="TERM"),
    "server-int-infinite": lambda cache: foreground_server(cache, signal_name="INT"),
    "rocq-timeout-control": rocq_timeout_control,
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", nargs="*")
    parser.add_argument("--repeat", type=int, default=1)
    args = parser.parse_args()
    for name in args.cases:
        if name not in CASES:
            parser.error(f"unknown case {name}; choices: {', '.join(CASES)}")
    check(ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0, "cannot become subreaper")
    subprocess.run(["direnv", "exec", ".", "dune", "build",
                    "@fmdeps/rocq-agent-toolkit/rocq-ed/install",
                    "@fmdeps/rocq-agent-toolkit/rocq-fake-repl/install"], cwd=ROOT, check=True)
    for _ in range(args.repeat):
        for name in args.cases or CASES:
            print(f"\n=== {name} ===", flush=True)
            try:
                with tempfile.TemporaryDirectory(prefix="rocq-ed-timeout-review-") as cache:
                    CASES[name](cache)
            finally:
                reap_descendants()
    print("\nAll selected rocq-ed timeout observations reproduced.", flush=True)


if __name__ == "__main__":
    main()
