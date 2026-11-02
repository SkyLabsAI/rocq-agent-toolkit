#!/usr/bin/env python3
"""Run review assertions against the unchanged feature branch (Linux).

The assertions describe correct behavior, so this exits nonzero on the reviewed
branch. A subreaper cleans up only this runner's test descendants, including
intentionally leaked helpers and detached supervisors.
"""
import argparse
import ctypes
import os
from pathlib import Path
import signal
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[5]
REL = Path("fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review")
BUILD = ROOT / "_build/default" / REL
CASES = {
    "kill-blocked-writer": ("kill-blocked-writer", None),
    "fork-kill-stopped-supervisor": ("fork-kill-stopped-supervisor", None),
    "kill-during-stop": ("kill-during-stop", None),
    "split-fork-window": ("split-fork-window", "after-fork"),
    "startup-fd-reuse": ("startup-fd-reuse", None),
    "deferred-cancel-failure": ("deferred-cancel-failure", "cancel-write-failure"),
    "guard-cloexec": ("guard-cloexec", "guard-atomic"),
    "second-pipe-failure": ("second-pipe-failure", None),
    "fork-pipe-failure": ("fork-pipe-failure", None),
    # Controls and an additional failure-path demonstration:
    "split-cancel-reap": ("split-cancel-reap", None),
    "split-after-reap": ("split-signal-boundary", "after-reap"),
    "idle-failure": ("idle-failure", None),
    "cancel-sigpipe": ("cancel-sigpipe", "cancel-write-failure"),
    "split-protocol-corruption": ("split-protocol-corruption", "both-fork-sides"),
    "fork-kill-idle-stopped-supervisor": ("fork-kill-idle-stopped-supervisor", None),
    "backtrack-ignores-interrupt": ("backtrack-ignores-interrupt", None),
    "cancelled-reset": ("cancelled-reset", None),
}
# Current-review matrix: ten fixed-behavior controls and three surviving findings.
# The binary's raw cancelled-backtrack probe is historical and is deliberately
# not exposed here: cooperative BackTo cancellation is now illegal.
DEFAULT = [
    "kill-blocked-writer", "split-fork-window", "split-protocol-corruption",
    "startup-fd-reuse", "guard-cloexec", "deferred-cancel-failure",
    "second-pipe-failure", "backtrack-ignores-interrupt", "idle-failure", "cancel-sigpipe",
    "fork-kill-stopped-supervisor", "kill-during-stop", "fork-pipe-failure",
]


def reap_descendants():
    deadline = time.monotonic() + 3
    while time.monotonic() < deadline:
        try:
            while os.waitpid(-1, os.WNOHANG)[0]:
                pass
        except ChildProcessError:
            return
        path = Path(f"/proc/{os.getpid()}/task/{os.getpid()}/children")
        for pid in map(int, path.read_text().split()):
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        time.sleep(0.01)
    raise RuntimeError("could not clean up test descendants")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", nargs="*", help="case names (default: current fixed/surviving-finding matrix)")
    parser.add_argument("--repeat", type=int, default=1)
    args = parser.parse_args()
    cases = args.cases or DEFAULT
    for name in cases:
        if name not in CASES:
            parser.error(f"unknown case {name!r}; choices: {', '.join(CASES)}")
    # PR_SET_CHILD_SUBREAPER: detached grandchildren stay owned by this runner.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0):
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_CHILD_SUBREAPER)")
    subprocess.run(
        ["direnv", "exec", ".", "dune", "build", str(REL / "repro.exe"),
         str(REL / "schedule.so")], cwd=ROOT, check=True)
    failures = 0
    for _ in range(args.repeat):
        for name in cases:
            binary_case, schedule = CASES[name]
            print(f"\n=== {name} ===", flush=True)
            command = ["direnv", "exec", ".", "env"]
            if schedule:
                command += [f"LD_PRELOAD={BUILD / 'schedule.so'}",
                            f"ROCQ_REVIEW_SCHEDULE={schedule}"]
            command += [str(BUILD / "repro.exe"), binary_case]
            def limit_fds():
                resource.setrlimit(resource.RLIMIT_NOFILE, (32, 32))
            process = subprocess.Popen(command, cwd=ROOT, start_new_session=True,
                                       preexec_fn=limit_fds if name == "second-pipe-failure" else None)
            try:
                code = process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                code = 124
            finally:
                reap_descendants()
            if code < 0:
                description = signal.Signals(-code).name
            else:
                description = str(code)
            print(f"result: {description}", flush=True)
            failures += code != 0
    print(f"\n{failures}/{len(cases) * args.repeat} correct-behavior assertions failed.")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
