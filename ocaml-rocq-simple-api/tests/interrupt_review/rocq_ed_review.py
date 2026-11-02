#!/usr/bin/env python3
"""Correct-behavior assertions for updated rocq-ed interruption (Linux).

Only test sessions are signalled/reaped. No production code is modified.
Failures exit nonzero; controls describe intended behavior and should pass.
"""
import argparse
import ctypes
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
from run import ROOT, reap_descendants
import rocq_ed_timeouts as h


class Session:
    def __init__(self, cache):
        self.cache = cache
        self.id, self.data, self.server, self.top = h.session(cache)

    def cli(self, name, *args, timed=None):
        return h.cli(self.cache, name, "-s", self.id, *args, timed=timed)

    def start(self, name, *args):
        return subprocess.Popen(h.command(self.cache, name, "-s", self.id, *args),
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def log(self):
        return (self.data / "log").read_text()

    def wait_log(self, needle):
        h.wait_for(lambda: needle in self.log(), f"missing log marker {needle!r}")

    def check_live(self):
        result = self.cli("status", "--context-lines=all", timed=["4s"])
        h.check(result.returncode == 0, f"session unavailable: {result.returncode}: {result.stderr}")
        return result.stdout


def timeout_control(cache, *, signal_name="TERM", foreground=False, finite=False):
    s = Session(cache)
    options = ["--signal", signal_name, "--kill-after=0.2s"]
    if foreground:
        options += ["--foreground"]
    options += ["0.2s"]
    result = s.cli("insert", "--text", h.FINITE if finite else h.LOOP, timed=options)
    h.check(result.returncode == 124, "client did not time out")
    if finite:
        time.sleep(1.2)
    status = s.check_live()
    h.check("Goal True" not in status, f"cancelled insertion was published: {status}")
    h.check("Client disconnected" in s.log(), "disconnect was not observed")
    goals = s.cli("goals", timed=["4s"])
    h.check(goals.returncode == 0 and "Not currently in a proof" in goals.stdout,
            f"backend did not restore the original proof state: {goals.stdout} {goals.stderr}")
    print("timed-out insertion was cancelled; unchanged document and live session", flush=True)


def explicit_control(cache, hard=False):
    s = Session(cache)
    h.check(s.cli("insert", "--text", "Goal True. Proof. ").returncode == 0, "proof setup failed")
    request = s.start("insert", "--keep=successful", "--text", "idtac. let rec loop := loop in loop.")
    s.wait_log("let rec loop")
    time.sleep(0.05)
    result = s.cli("interrupt", *(["--kill"] if hard else []), timed=["4s"])
    h.check(result.returncode == 0, f"interrupt failed: {result.stderr}")
    out, err = request.communicate(timeout=6)
    h.check(request.returncode == 1 and "User interrupt" in out + err,
            f"interrupted request did not return ordinary error: {request.returncode}: {out} {err}")
    status = s.check_live()
    h.check("idtac." in status and "let rec loop" not in status, "keep=successful not preserved")
    finish = s.cli("insert", "--text", "exact I. Qed.")
    h.check(finish.returncode == 0, f"proof state was not reusable: {finish.stdout} {finish.stderr}")
    print(f"explicit {'hard' if hard else 'cooperative'} interrupt returns error=1, keeps successful prefix", flush=True)


def disconnect_hard_control(cache):
    s = Session(cache)
    request = s.start("insert", "--text", h.LOOP)
    s.wait_log("let rec loop")
    time.sleep(0.05)
    os.killpg(s.top, signal.SIGSTOP)
    request.kill()
    request.communicate(timeout=3)
    status = s.check_live()
    h.check("Goal True" not in status, "cancelled hard-killed insertion was published")
    h.check("Interruption timed out; killed" in s.log() and "Rocq backend restarted." in s.log(),
            "disconnect did not escalate and restart")
    goals = s.cli("goals", timed=["4s"])
    h.check(goals.returncode == 0 and "Not currently in a proof" in goals.stdout,
            "restarted backend did not restore the original proof state")
    print("disconnected client with SIGSTOPed backend was hard-killed/restarted; document unchanged", flush=True)


def stalled_interrupt_reader(cache):
    s = Session(cache)
    peer = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    peer.connect(str(s.data / "interrupt.socket"))
    try:
        time.sleep(0.05)
        interrupt = s.cli("interrupt", timed=["0.3s"])
        stop = s.cli("stop", timed=["3s"])
        h.check(stop.returncode == 0, f"stop failed: {stop.returncode}: {stop.stderr}")
        time.sleep(0.1)
        server_still_alive = h.alive(s.server)
        top_still_alive = h.alive(s.top)
        print(f"second interrupt exit={interrupt.returncode}; stop exit=0; "
              f"server alive={server_still_alive}; backend alive={top_still_alive}", flush=True)
        h.check(not server_still_alive and not top_still_alive,
                "a stalled interrupt-socket reader prevents shutdown after stop acknowledged success")
    finally:
        peer.close()
        h.wait_for(lambda: not h.alive(s.server) and not h.alive(s.top),
                   "shutdown did not finish after closing the stalled control peer")
        print("closing the stalled control peer releases shutdown", flush=True)


def queued_delete(cache):
    s = Session(cache)
    before = s.check_live()
    blocker = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    blocker.connect(str(s.data / "socket"))
    try:
        time.sleep(0.05)
        result = s.cli("delete", "--count-items=all", timed=["0.2s"])
        h.check(result.returncode == 124, "queued client did not time out before execution")
    finally:
        blocker.close()
    after = s.check_live()
    print(f"queued delete client=124; before={before.strip()!r}; after={after.strip()!r}", flush=True)
    h.check(after == before, "a client dead before request execution still published its deletion")


def queued_delete_during_recovery(cache):
    s = Session(cache)
    before = s.check_live()
    request = s.start("insert", "--text", h.LOOP)
    s.wait_log("let rec loop")
    time.sleep(0.05)
    # Force the documented 0.5-second escalation/restart path to leave a real
    # queueing window. All user requests below are genuine rocq-ed CLI calls.
    os.killpg(s.top, signal.SIGSTOP)
    request.kill()
    request.communicate(timeout=3)
    result = s.cli("delete", "--count-items=all", timed=["0.15s"])
    h.check(result.returncode == 124, f"queued delete did not time out: {result.returncode}: {result.stderr}")
    after = s.check_live()
    print(f"delete timed out during prior request recovery; before={before.strip()!r}; after={after.strip()!r}", flush=True)
    h.check(after == before, "timed-out queued deletion was applied after backend recovery")


def commit_fifo(cache):
    s = Session(cache)
    h.check(s.cli("insert", "--text", "Definition committed := 0.").returncode == 0, "setup failed")
    fifo = Path(cache) / "commit.v"
    os.mkfifo(fifo)
    request = s.start("commit", "--force", "--file", str(fifo))
    s.wait_log("Request [Commit")
    time.sleep(0.05)
    request.kill()
    request.communicate(timeout=3)
    time.sleep(0.7)
    interrupt = s.cli("interrupt", "--kill", timed=["0.5s"])
    status = s.cli("status", timed=["0.3s"])
    print(f"after commit-client death: interrupt={interrupt.returncode} {interrupt.stdout.strip()!r}; "
          f"status={status.returncode}", flush=True)
    h.check(status.returncode == 0, "client disconnect leaves host-side commit blocked with no interruptible backend operation")


def foreground_timeout(cache, *, signal_name="TERM"):
    # Existing diagnostic asserts the surviving private process; turn its
    # observation into a correct-behavior failure in this current-review runner.
    h.foreground_server(cache, signal_name=signal_name)
    raise AssertionError("foreground timeout leaves the busy private process running")


CASES = {
    "timeout-control": timeout_control,
    "timeout-int-control": lambda cache: timeout_control(cache, signal_name="INT"),
    "timeout-foreground-control": lambda cache: timeout_control(cache, foreground=True),
    "timeout-finite-control": lambda cache: timeout_control(cache, finite=True),
    "interrupt-control": explicit_control,
    "hard-interrupt-control": lambda cache: explicit_control(cache, hard=True),
    "disconnect-hard-control": disconnect_hard_control,
    "stalled-interrupt-reader": stalled_interrupt_reader,
    "queued-delete": queued_delete,
    "queued-delete-during-recovery": queued_delete_during_recovery,
    "commit-fifo": commit_fifo,
    "foreground-timeout": foreground_timeout,
    "foreground-int-timeout": lambda cache: foreground_timeout(cache, signal_name="INT"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", nargs="*")
    parser.add_argument("--repeat", type=int, default=1)
    args = parser.parse_args()
    for name in args.cases:
        if name not in CASES:
            parser.error(f"unknown case {name}; choose from {', '.join(CASES)}")
    h.check(ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0, "cannot become subreaper")
    subprocess.run(["direnv", "exec", ".", "dune", "build",
                    "@fmdeps/rocq-agent-toolkit/rocq-ed/install",
                    "@fmdeps/rocq-agent-toolkit/rocq-fake-repl/install"], cwd=ROOT, check=True)
    failures = 0
    for _ in range(args.repeat):
        for name in args.cases or CASES:
            print(f"\n=== {name} ===", flush=True)
            try:
                with tempfile.TemporaryDirectory(prefix="rat-current-") as cache:
                    CASES[name](cache)
            except Exception as error:
                failures += 1
                print(f"FAIL: {error}", flush=True)
            else:
                print("PASS", flush=True)
            finally:
                reap_descendants()
    print(f"\n{failures} assertion failures", flush=True)
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
