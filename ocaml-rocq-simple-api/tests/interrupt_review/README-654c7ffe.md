# Interrupt feature review and executable reproducers

**Verdict: request changes. Nine implementation defects and one additional
shutdown-design gap reproduced.**

Reviewed `rodolphe/toplevel-interupt` at `654c7ffeb0c428313e3d2644741ee6927d045e35`
against `main` / `origin/main` at `53fde9a9`. Both commits and all seven changed
files were reviewed: the public implementation/interface, private executable,
protocol types, Dune test registration, interrupt tests, and `PROTOCOL.md`.
Paths and production line numbers below refer to that revision.

## Run the evidence

From the **workspace root**:

```sh
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/run.py
```

Run an individual case, or repeat the entire set:

```sh
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/run.py cancelled-backtrack
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/run.py --repeat 3
```

These are assertions of **correct behavior**, not tests that consider a bug a
success. On the reviewed branch the default ten cases all fail, and the runner
exits **1**. A crash by SIGPIPE is reported as `SIGPIPE`, not disguised as an OCaml
exception. Cases are opt-in, not registered under the normal `runtest` alias.
No production source was changed or copied into the tests.

Requirements: the composed workspace toolchain, Linux `/proc` and subreaper
support, Python 3, `direnv`, a C compiler, and `prlimit` from util-linux. The runner
builds from the workspace root through `direnv`, bounds each case, and reaps only
its own test descendants, including intentionally leaked helpers and detached
supervisors. Resource limits are lowered only in disposable test processes.

Most cases use only the public API and real OS process operations. The late
backtrack cancellation uses the documented **real private protocol** to select a
legal ordering deterministically. `schedule.c` supplies scheduling/fault hooks:

- pause the real splitter fork before OCaml installs resource ownership;
- close the real child's command reader immediately before it sends `Started`;
- pause the real `F_SETFD(FD_CLOEXEC)` call to expose concurrent descriptor inheritance.

The hooks do not replace the implementation or fabricate successful syscall
results. The splitter and FIFO inheritance cases use actual public API calls
from concurrent threads/domains. Supplementary cases are listed below.

## 1. [P1] Killing a blocked request writer kills the API application

**Locations:** `lib/api/rocq_toplevel.ml:91–98,195–203,240–249,413–418`.

`kill` accepts `Preparing`, so it can kill the pipe reader while the active
request is still being flushed. A broken-pipe write generates SIGPIPE in the
**API host**, whose default signal disposition terminates it. OCaml exception
handlers do not prevent this. Cancellation and supervisor-control writes have
the same exposure.

**Case:** `kill-blocked-writer`. Stop the real private process, send a 1 MB request
on a worker, then call public `kill`. **Observed:** process termination by
`SIGPIPE` (shell status 141), instead of `Interrupted Killed`.

`cancel-sigpipe` separately reproduces the new cancellation-publication path;
`idle-failure` demonstrates the pre-existing general dead-reader vulnerability.
The blocked-writer scenario is specifically enabled by the newly added `kill`.

**Required:** safe transport writes under the default signal disposition,
including when cancellation/kill races with a writer. Add subprocess tests; a
host that has globally ignored SIGPIPE masks this problem.

## 2. [P1] Splitter interruption can leak resources and corrupt the protocol

**Locations:** `bin/private-toplevel/main.ml:478–525`, especially `:500` and `:521`.

The splitter forks with SIGINT unblocked. The parent has not yet entered the
cleanup handler that owns its new PID and pipes, and the helper has not yet
installed its exit-on-exception boundary or disconnected protocol stdout.
Interruption can escape the fork boundary into the inherited `run_request`
handler in either process.

**Case:** `split-fork-window`. Pause return from the real parent-side fork,
call public `interrupt`, then release it. **Observed:** `Interrupted Interrupt`
returns, but `/proc/<top>/children` still contains the splitter and the private
process's open-FD count grows from **5 to 7**.

**Additional case:** `split-protocol-corruption`. Hold both fork branches until
the real API publishes cancellation, then let the helper return first. The
helper runs the inherited server exception handler, writes its own terminal
response/acknowledgement, and reads the real command stream. When the original
owner resumes it writes another terminal response. **Observed:** the split
reports cooperative interruption, but the next `Check I.` fails with
`Interrupted (Failed (Failure "mismatched toplevel start response"))`.

**Required:** mask SIGINT across pipe/fork acquisition and ownership transfer;
unmask only after the parent's PID/FD cleanup is installed and the child has
isolated its protocol descriptors and installed an unconditional exit boundary.

## 3. [P1] Cancelling a completed BackTo acknowledges a deleted state

**Locations:** `bin/private-toplevel/main.ml:542–544,594–600`.

`Stm.edit_at` destructively discards later states. Rolling back a completed
`BackTo` with another `edit_at` cannot restore the state it deleted. `rollback`
then silently discards the returned `Error` and acknowledges the old, now
expired SID as if restoration succeeded.

**Case:** `cancelled-backtrack`. Create two definitions at SIDs 2 and 3, complete
`BackTo 2`, then send the legal late `Cancel`/SIGINT/fence sequence before
`Continue`. **Observed:** cancellation acknowledges **SID 3**, but checking the
second definition returns `Anomaly "Uncaught exception Stm.Vcs_aux.Expired."`.

**Required:** a genuinely restorable document snapshot/transaction for destructive
navigation, or a different commit/cancellation design. Never acknowledge failed
rollback as successful, reusable cooperative interruption.

## 4. [P1] Startup failure closes descriptors owned by unrelated threads

**Locations:** `lib/api/rocq_toplevel.ml:138–144,152–153`.

The parent closes `command_in` and `response_out` after spawning, then closes the
same numeric descriptors again during startup-error cleanup. Another thread can
reuse those numbers during the handshake. The other two pipe ends are also
closed as raw descriptors and again through their channels.

**Case:** `startup-fd-reuse`. Initialize the real executable with a `.v` startup
file that publishes readiness and loops. Open an unrelated `/dev/null` descriptor
while initialization waits, then kill the initializing private process.
**Observed:** the unrelated descriptor becomes `EBADF` after `init` cleanup.

**Required:** explicit ownership transfer; remove closed/transferred descriptors
from raw cleanup ownership and close every resource exactly once.

## 5. [P1] FIFO guards leak into concurrent subprocesses

**Locations:** `lib/api/rocq_toplevel.ml:500–503`.

`open_guard` opens a read-write FIFO without `O_CLOEXEC`, then sets close-on-exec
in a separate operation. Concurrent process creation in that interval inherits
the guard; setting the flag later cannot fix the inherited descriptor.

**Case:** `guard-cloexec`. Pause setting the `in` guard's flag, initialize another
real toplevel from a concurrent OCaml domain, then finish the fork and stop its
child. **Observed:** the forked child remains alive after `stop`, and exits only
when the unrelated toplevel stops and releases the inherited guard. The guard
prevents stdin EOF; the handle has already become `Stopped Normal`.

**Required:** atomic close-on-exec creation, e.g.
`Unix.openfile path [O_RDWR; O_CLOEXEC] 0`.

## 6. [P1] Forked hard kill depends on a responsive supervisor

**Locations:** `lib/api/rocq_toplevel.ml:91–106`;
`bin/private-toplevel/main.ml:340–350`.

For a forked handle, `cleanup ~kill:true` only sends `Supervisor_kill`; it does
not signal the actual toplevel. If the supervisor is stalled, closing the
response channel can then wait on the active request's channel lock forever.

**Case:** `fork-kill-stopped-supervisor`. Run a looping tactic in a forked child,
SIGSTOP only its supervisor, then call public `kill`. A bounded watchdog resumes
the supervisor after 0.3 seconds. **Observed:** `kill` hangs until that external
SIGCONT (approximately **0.314 s**). Without the watchdog it never completes.

`fork-kill-idle-stopped-supervisor` demonstrates the idle version: `kill` returns
successfully while the actual child remains running.

**Required:** forced termination must not depend indefinitely on supervisor
responsiveness. Preserve PID-reservation safety while making actual termination
and acknowledgement reliable; merely marking the handle killed is insufficient.

## 7. [P2] Deferred cancellation publication reports the wrong exception

**Locations:** `lib/api/rocq_toplevel.ml:207–212,332,443–445`.

If interruption was latched during `Preparing`, the request thread itself calls
`publish_cancellation`. On publication failure it raises `Stopped (Failed e)`,
which `request` explicitly rethrows instead of translating to an active-operation
failure.

**Case:** `deferred-cancel-failure`. Latch interruption during a blocked request
write; let the real peer close its command reader before sending `Started`.
Ignore SIGPIPE here to isolate this from finding 1. **Observed:** the active
`loc_after_blanks` raises `Stopped (Failed _)`, not `Interrupted (Failed _)`.

**Required:** distinguish request-thread publication from external `interrupt`
publication, or route the request-side error through `fail_request`.

## 8. [P2] Failure allocating the second startup pipe leaks the first

**Locations:** `lib/api/rocq_toplevel.ml:133–134`.

Both allocations precede the cleanup boundary. If the response-pipe allocation
fails, the command pipe's two raw descriptors have no cleanup owner.

**Case:** `second-pipe-failure`. In a subprocess with RLIMIT_NOFILE=32, fill the
FD table, release three slots, and call `init`. **Observed:** `Unix.EMFILE` and
available descriptor slots **3 -> 1**. Garbage collection cannot close raw FDs.

**Required:** protect the first pipe before attempting the second. Fixing
finding 4 inside the existing cleanup function does not cover this earlier error.

## 9. [P2] Fork resource exhaustion kills the source toplevel

**Locations:** `bin/private-toplevel/main.ml:366–367,404–419,573–575`.

The new PID-reporting `Unix.pipe` is outside the launcher's Unix-error handler.
`fork` restores the signal mask but rethrows the error; `run_request` propagates
it out of the server instead of returning a creation-error result.

**Case:** `fork-pipe-failure`. After initializing a real source, lower only its
FD limit with `prlimit --pid <pid> --nofile=3:3` and call public `fork`.
**Observed:** the private executable exits on `Unix.EMFILE`; the API reports
`Interrupted (Failed End_of_file)`. A recoverable fork-creation error has destroyed
the source, rather than returning `Error message` as the interface promises.

**Required:** translate pipe-allocation failure into the ordinary Fork error
result without terminating or mutating the source toplevel.

## 10. [P2; design gap] Kill cannot rescue a hung graceful stop

**Locations:** `lib/api/rocq_toplevel.ml:184–189,243` and `:90–106`.

`kill` waits while the state is `Stopping`. `stop` may already be waiting
indefinitely in `waitpid`; the cleanup `closed` flag has also been claimed.
Consequently the force-stop operation cannot escalate a blocked graceful stop.

**Case:** `kill-during-stop`. SIGSTOP an idle direct child, start public `stop`,
then call public `kill`. A watchdog SIGCONTs the child after 0.3 seconds.
**Observed:** `kill` waits for that external rescue, then raises `Stopped Normal`
instead of forcing termination. Without the watchdog both calls remain stuck.

The protocol document explicitly specifies waiting in `Stopping`, so this is a
**design limitation**, not a discrepancy between that state table and the code.
If `kill` is intended as the unconditional escape hatch, support coordinated
`Stopping -> Killing` escalation; otherwise document this important exception to
the force-stop guarantee in the public interface.

## Practical triggerability in the current rocq-ed CLI

### Scope and important reachability limits

Cross-package paths in this section are relative to
`fmdeps/rocq-agent-toolkit/`; findings 1–10 above use paths relative to its
`ocaml-rocq-simple-api/` package.

The P1/P2 labels above describe **consequence and library correctness**, not a
measured frequency of failure during editing. The estimates below are qualitative
source-based reachability assessments, supplemented by real CLI experiments;
they are **not statistical rates**. A scheduling shim that reproduces a race on
every run does not mean a user will hit that race on every edit.

At this revision, stock `rocq-ed` does **not use the new cancellation feature**:

- `rocq-ed/src/protocol.ml:209–242` accepts and executes one request
  synchronously. It cannot process a separate cancellation request while a
  tactic is running. The command list has no interrupt/kill command.
- There are **no calls to `Rocq_toplevel.interrupt` or `Rocq_toplevel.kill`**
  on the `rocq-ed`/document-manager execution path. GNU `timeout` sends OS signals;
  it does not manufacture the protocol's `Cancel`/signal-fence/acknowledgement.
- Atomic insertion uses `Document.clone` (`rocq-ed/src/request.ml:305`), which
  shares the same backend (`rocq-doc-manager/lib/document.ml:100–105`). It does
  **not** fork a Rocq process. The physical fork is in `Document.materialize`
  (`document.ml:107–123`), which the `rocq-ed` CLI never calls.
- Concurrent shell invocations are separate processes. They do not share a
  descriptor table. Multiple clients/sessions alone do not supply the in-process
  thread/domain concurrency required by findings 4 and 5.

Thus most exact triggers below are dormant in the current CLI, even though they
are real defects in an independently usable library. Wrapping a CLI command in
`timeout`, including `timeout -s INT` or `timeout -k ...`, does **not** by itself
make those API-only paths reachable.

| Finding | Ease in stock rocq-ed, including ordinary external timeouts | Necessary additional conditions |
| --- | --- | --- |
| **1 — API pipe SIGPIPE** | **Exact kill/write race: not exercised.** The general dead-private-reader variant is possible after an unexpected backend death, but is not an ordinary editing event. | The reviewed hard-kill race requires an API `kill` racing a request write. An OOM kill or explicit termination of the private process can expose a broken-pipe write without that API. Do not confuse this with the easy frontend-socket SIGPIPE described below. |
| **2 — splitter fork window** | **Not normally exercised by CLI timeouts.** Splitting itself is common during initialization/insertion; the missing ingredient is SIGINT delivered to the **private** process at its fork boundary. | A custom wrapper/operator that signals the private process/group, or future API cancellation integration. The uninstrumented window is narrow and scheduler-dependent; repeated interrupts/load can increase exposure. A long tactic alone is not this trigger. |
| **3 — cancelled BackTo** | **Exact late-cancellation path: not exercised.** Ordinary rewind/replay can use `BackTo`, but no CLI code sends `Cancel`. | A library client/future adapter must cancel during destructive navigation. Neither killing the frontend nor merely selecting `timeout -s INT` sends a late protocol cancellation. |
| **4 — startup descriptor double-close** | **Very unlikely in stock CLI use.** Startup failure is plausible; reuse by other work in the same host process is normally absent. | Concurrent FD-opening activity in the **same** API process during failed initialization. Starting another `rocq-ed` process does not supply that reuse. A timeout terminating the host is also not a cleanup double-close execution. |
| **5 — inherited FIFO guards** | **Not exercised by this CLI.** | Both a physical toplevel fork (absent here) and concurrent process creation in the same FD-owning process during the non-atomic close-on-exec interval. Atomic edits and multiple independent sessions do not qualify. |
| **6 — stalled fork supervisor** | **Not exercised by this CLI.** | A materialized/forked handle, API `kill`, and an unresponsive supervisor. An expensive proof does not itself stall the supervisor. GNU `timeout -k` is an OS signal operation, not this API call. |
| **7 — wrong deferred-failure exception** | **Not exercised by this CLI.** | Latched API interruption plus transport failure during publication; observing the wrong exception also requires getting past the SIGPIPE problem. It is a compound fault even for direct API users. |
| **8 — second startup pipe failure** | **Reachable but rare under normal resource limits.** All sessions initialize a direct toplevel, so this is not behind an unused API. | Per-process FD limits or system-wide file-table pressure must permit the first pipe and reject the second. Long files alone do not imply FD exhaustion. In stock CLI startup failure, the host normally exits, reclaiming the leak; repeated library retries in a long-lived host are worse. Timeouts may add indirect resource pressure, not an automatic per-process leak trigger. |
| **9 — fork pipe exhaustion** | **Not exercised by this CLI.** | Physical `Document.materialize`/API fork plus allocation failure in the source process. Many normal inserts do not take this path. |
| **10 — kill cannot escalate stop** | **Exact API race: not exercised.** A blocked session/shutdown can still be user-visible, but is not evidence of this particular state-machine race. | One thread in API `stop`, another calling API `kill`. The CLI has neither that concurrent request handling nor the force-kill call. Killing an OS process externally is a different operation. |

**Practical estimate:** with healthy dependencies and ordinary resource limits,
none of the nine implementation bugs should be described as an expected failure
on routine sequential `rocq-ed` edits. Most require missing API integration,
in-process concurrency, or exceptional resource/process failures. That does
**not** make external timeouts safe: the following much easier failures are
already reachable without invoking the new APIs.

### What GNU timeout actually reaches

Observed with GNU coreutils `timeout` **9.12**. By default it sends SIGTERM to
the monitored command/process group; `-s INT` changes the signal, not the target
into a recursive process-tree traversal. `--foreground` does not add descendant
coverage. `-k` escalates only within the monitored target scope; it does not find
processes that have created different sessions/groups.

There are two independent isolation boundaries:

1. The default `rocq-ed init` double-forks and calls `setsid`
   (`rocq-ed/src/protocol.ml:33–101`). Later `rocq-ed insert/move/status/stop`
   invocations are clients of that detached daemon.
2. The feature branch makes the **private Rocq process** call `setsid` too
   (`ocaml-rocq-simple-api/bin/private-toplevel/main.ml:12–14`). It therefore
   escapes even a foreground server's timeout process group.

| Command being timed out | Likely/observed outcome once a request has reached the server |
| --- | --- |
| `timeout T rocq-ed insert ...` / `move ...` | The client is terminated, **not the daemon or tactic**. An infinite computation continues and subsequent requests can wait indefinitely. If work later finishes, replying to the dead client can kill the daemon with SIGPIPE. |
| Same, with `-s INT`, `-k ...`, or `--foreground` | Does not turn the deadline into cooperative cancellation or fix the detached-server boundary. The infinite-work cases were reproduced with each of these options; the tested client cases also include `-k`. |
| `timeout T rocq-ed init FILE.v` | Normally `init` returns after readiness, so the timeout ceases to supervise anything and is **not a session lifetime limit**. If startup itself times out, timing matters: dependency work may still be attached, or daemon/private startup may already have detached. There is no reliable recursive cleanup guarantee; a later readiness write to the dead initializing client can also fail. This startup-deadline variant was inferred from the code, not measured with a forced startup stall. |
| `timeout -k K T rocq-ed init --no-daemon FILE.v` | The foreground **server** dies on the deadline, but a **busy private toplevel survives in its own session**. An infinite tactic keeps consuming CPU. An idle private process may instead exit after seeing command-pipe EOF; the persistent orphan observation specifically requires in-flight work that does not return to protocol I/O. |
| Timing out `rocq-ed stop` | This is still a timeout of a client, not a force-stop API. The server cannot service Stop while synchronously running another request. Even an accepted Stop is acknowledged before final `Document.stop` cleanup (`protocol.ml:229–255`), so client success/exit alone does not prove all backend processes were reaped. |

The foreground busy-process escape is an important **integration consequence of
this branch's added private `setsid`**, not one of the API race reproducers above.
The base implementation had no such private-session creation in the reviewed
source path. Group membership and surviving work were measured on this branch;
the base binary was **not rebuilt for an A/B comparison**. In contrast, the
frontend-disconnect/reply problem is in unchanged `rocq-ed` socket code and
should not be reported as a newly introduced `Rocq_toplevel.kill` regression.

### Real CLI evidence and ease of reproduction

Run the additional opt-in diagnostic from the workspace root:

```sh
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/rocq_ed_timeouts.py --repeat 2
```

This uses the real installed `rocq-ed`, real GNU `timeout`, and a tiny composed
Dune fixture in `rocq_ed_fixture/`. Initialization uses the normal dependency
build path, **not** `--no-build-deps` or `dune --root`. There are **no preload
hooks, fake peers, SIGSTOP scheduling tricks, or lowered resource limits** in
these CLI cases. Sessions/caches are isolated and the subreaper kills/reaps the
diagnostic's own surviving processes afterward.

Unlike `run.py`, these diagnostics assert that the documented **problematic
observation** occurs, so a fully reproduced diagnostic run exits **0**.

Six timeout cases were each repeated twice: **12/12 observations reproduced**:

- **`client-term-infinite`, `client-int-infinite`,
  `client-foreground-infinite`: easy/deterministic after dispatch.** Insert
  `Goal True. Proof. let rec loop := loop in loop.` under an external 0.2-second
  deadline. The client returns **124**; the real daemon/private process remain
  alive, CPU ticks continue increasing, and a subsequent `status` also times out
  with **124**. No cancellation happens. These cases include `-k 0.2s`; changing
  to INT or GNU `--foreground` does not help.
- **`client-term-finite`: easy/deterministic once the client dies before the
  reply.** Insert `Goal True. Proof. Timeout 1 let rec loop := loop in loop.`
  under the same 0.2-second external deadline. Client returns **124**. About one
  second later Rocq's own timeout ends the tactic; the daemon logs `Sending
  response.` and dies by **SIGPIPE**, confirmed by `waitpid` (not just inferred
  from a missing PID). A new `status` returns **123**, reporting a crashed/killed
  session. This is the **frontend Unix-socket write** at
  `rocq-ed/src/protocol.ml:230–232`, not finding 1's private pipe write. No rare
  fork/rollback interleaving is needed.
- **`server-term-infinite`, `server-int-infinite`: easy/deterministic for a busy
  foreground session.** Run `init --no-daemon` under a three-second external
  deadline with `-k 0.2s`, and submit the infinite tactic before expiry. Timeout
  returns **124**, the server is dead, and the private process still consumes
  CPU in its separate session. The in-flight client sees EOF/error **125**.
  TERM and INT both reproduce this. Changing signal alone cannot repair a target
  scope that excludes the private process.

The additional **`rocq-timeout-control`** was also repeated twice: both passes
show that allowing Rocq's own `Timeout 1` to finish **without prematurely killing
the client** gives an ordinary command error **1**, followed by a successful
`status` **0** and a live session. Rocq's vernacular timeout and an external
wall-clock timeout of a CLI process are not interchangeable. The native timeout
is useful for supported commands, but is not a universal wall-clock/OS-process
cleanup guarantee for arbitrary plugins or external side effects.

These examples intentionally include an infinite or one-second tactic to make
the deadline mismatch easy to see. A real long-running tactic, slow query, or
large operation can produce the same disconnected-client condition. The
practical trigger is **the request outliving its client**, not the spelling of
the sample loop. The observations give no population-wide percentage of normal
editing operations that will exceed a user's chosen deadline.

**Operational conclusion:** do not treat exit 124 from an external `timeout` as
proof that proof search stopped, that edits were rolled back, or that the
session was reaped. A timed-out mutating request may still apply changes before
its late reply fails. Do not blindly retry the mutation. Once an infinite
request is running, a queued `rocq-ed stop` is not a reliable rescue; a supervising
process must account for the actual owned daemon/private process groups (or use
a lifecycle container/cgroup), rather than only the frontend PID. No destructive
cleanup of unrelated sessions is performed by these diagnostics.

Before advertising timeout-safe editing, the CLI needs explicit cancellation
and transaction/lifetime integration, plus safe handling of disconnected-client
responses. The dormant low-level bugs must also be fixed before wiring those
APIs into the CLI, because that wiring would make their triggers substantially
more practical.

## Validation and coverage

These composed-workspace commands **pass**:

```sh
direnv exec . dune build \
  @fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/all \
  @fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/install \
  @fmdeps/rocq-agent-toolkit/rocq-ed/install
direnv exec . dune runtest --force \
  fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests \
  fmdeps/rocq-agent-toolkit/rocq-ed/tests
```

The new evidence was repeated against the unchanged implementation:

- Default ten cases, three repetitions: **30/30 intentional assertion failures**.
- `split-protocol-corruption`, `cancel-sigpipe`, `idle-failure`, and
  `fork-kill-idle-stopped-supervisor`, three repetitions: **12/12 failures**.
- Controls `split-cancel-reap` and `split-after-reap`, three repetitions:
  **6/6 passes**. Interruption after ownership registration/reaping does not
  reproduce the unsafe fork-entry window.

Run the controls and supplementary cases by passing those names to `run.py`.
No full-workspace build/test was attempted.

The existing tests pass because they do not exercise these boundaries: blocked
request writes during kill, both sides of splitter fork entry, destructive
late cancellation, concurrent startup FD reuse/inheritance, allocation failures,
publication failures, or stalled termination supervision. `PROTOCOL.md` claims
transactional rollback and process/descriptor ownership properties that these
executions contradict. A clean existing `runtest` is therefore not evidence that
the feature is complete.
