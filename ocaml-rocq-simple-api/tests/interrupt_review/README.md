# Updated interruption review: backend, document manager, and rocq-ed

**Verdict: request changes.** Most original backend defects are fixed, and the
CLI now genuinely implements interruption. Two new CLI bugs, the foreground
process-lifetime problem, two surviving backend bugs, and two explicitly
identified design/scope limitations are reproduced below.

## Revision and scope

- Current branch: `rodolphe/toplevel-interupt`.
- Current HEAD: **`0200345fd76b2e079050497c1a01730684bc1b24`**.
- Base: `origin/main` / `53fde9a9291b5a8bfc396bfa24e7fe465ba90232`.
- Previously reviewed, outdated HEAD: `654c7ffeb0c428313e3d2644741ee6927d045e35`.
- Reviewed all **24 changed files**, including implementation, interfaces,
  dependencies/OPAM metadata, protocol documentation, and tests. Also compared
  the new state directly with the previous reviewed revision.

This report **supersedes** [the archived old report](README-654c7ffe.md), including
its statement that rocq-ed does not use interruption. That statement is false at
this HEAD. All production paths/line numbers below are relative to
`fmdeps/rocq-agent-toolkit/` at the current revision.

No production files were changed for this review. Only opt-in evidence and this
report were added/adapted. Existing user review files elsewhere were untouched.

## What the updated branch actually implements

- Public `Document.interrupt` / `Document.kill` expose the active toplevel without
  waiting for the document's backend mutex; operation bookkeeping and exception
  propagation were adjusted to survive interruption.
- `rocq-ed interrupt` and `rocq-ed interrupt --kill` use a separate Unix socket
  and control thread, bypassing the ordinary client lock.
- A per-request watcher observes frontend disconnection, requests cooperative
  interruption, and escalates after **0.5 seconds** if an active backend remains.
- Requests run on working document clones. Their metadata is published only if
  the request wins `Running -> Publishing`; a watcher can instead win
  `Running -> Cancelled`. A killed/failed backend is restarted as necessary.
- SIGPIPE is ignored in the running CLI server; late response-write failures are
  logged rather than killing the daemon. The independently usable backend API
  also protects its own writes without relying on this global disposition.

These are substantive end-to-end changes, not merely unused library facilities.
The normal interruption paths work in both the supplied tests and the additional
controls below. Physical `Document.materialize` / `Rocq_toplevel.fork` is still
**not** used by stock rocq-ed; `Document.clone` shares a backend and does not fork.

## Disposition of every original finding

Old numbers refer to `README-654c7ffe.md`.

| Old finding | Current disposition and executable check |
| --- | --- |
| **1. API-host SIGPIPE during kill/write** | **Fixed.** Per-thread masking/draining covers writes and output closes (`ocaml-rocq-simple-api/lib/api/rocq_toplevel.ml:51–68`). `kill-blocked-writer`, `cancel-sigpipe`, and `idle-failure` now pass with the default disposition where applicable. |
| **2. Splitter fork interruption corrupts protocol/leaks resources** | **Fixed.** SIGINT is blocked across acquisition/fork until both ownership boundaries are installed (`bin/private-toplevel/main.ml:474–584` within the API package). Both fork-window reproducers now pass, with no child left and FD count **5 -> 5**. |
| **3. Late BackTo cancellation acknowledges an expired state** | **Addressed by a documented contract change.** BackTo no longer accepts cooperative interruption, and rollback failure is checked. The raw old probe now sends an **illegal** Cancel and must not be counted as a surviving bug. The new public-API `backtrack-ignores-interrupt` control passes. This is not transactional backtracking; it is intentional non-cancellability. |
| **4. Startup cleanup closes unrelated descriptors** | **Fixed.** Owned descriptor references and channel ownership transfer prevent repeated closes (`lib/api/rocq_toplevel.ml:154–233` within the API package). `startup-fd-reuse` passes using the real initializing executable. |
| **5. FIFO guard inheritance race** | **Fixed.** Guards are created with `O_CLOEXEC` (`lib/api/rocq_toplevel.ml:570–571`). The adapted hook pauses immediately after the actual open, before any later setter could repair it. Concurrent initialization no longer inherits the guard; `guard-cloexec` passes. The old setter-delay hook would simply stop firing, which alone would not prove the fix. |
| **6. Forked hard kill depends on supervisor responsiveness** | **Survives.** See B1. |
| **7. Deferred cancellation reports Stopped instead of Interrupted** | **Fixed.** Publication returns an error to its caller, and request-side activation translates it to `Interrupted (Failed _)`. `deferred-cancel-failure` passes. |
| **8. Second startup pipe failure leaks the first** | **Fixed.** The second allocation now has first-pipe cleanup. `second-pipe-failure` reports available slots **3 -> 3**, not 3 -> 1. |
| **9. Fork pipe exhaustion destroys the source** | **Survives.** See B2. |
| **10. Kill cannot escalate a hung stop** | **Survives as a design limitation**, not a mismatch with the documented state table. See L1. |

The old practical timeout analysis also needed revision: active frontend timeouts
now cancel ordinary proof requests, and late frontend replies no longer kill the
daemon by SIGPIPE. The separate **foreground-server** lifetime escape survives.
Do not run the old `rocq_ed_timeouts.py` default suite and interpret its obsolete
bad-behavior expectations as current failures; it remains as historical evidence
and a helper module. Use `rocq_ed_review.py` for current assertions.

## Current findings

### C1. [P1] A queued request can mutate the document after its client already timed out

**Locations:** `rocq-ed/src/protocol.ml:166–196,501–518,554–569`;
`rocq-ed/src/request.ml:392–399`.

The server creates the disconnect-watcher thread, but does not synchronously
check for an already disconnected peer or wait for the watcher's initial check.
It immediately executes the request. A short, metadata-only operation such as
Delete can finish and win `Running -> Publishing` before the watcher gets CPU.
`finish_watcher` then stops the observer and the deletion is copied into the
session even though the client was dead **before execution began**.

This is not the legitimate ambiguity where an operation finished/published and
only then its reply was lost. The examples keep the request queued until after
GNU timeout has terminated its frontend, and only then permit execution.

**Reproducers:** `queued-delete` and `queued-delete-during-recovery`.

1. The fixture has an unprocessed comment in its suffix.
2. Queue a real `rocq-ed delete --count-items=all` under a 0.2-second deadline
   behind a connection currently blocking ordinary request decoding.
3. Wait for that client to exit **124**, then release the earlier connection.
4. Query the document with a new live client.

**Observed, three repetitions:**

```text
queued delete client=124
before: 1| <CURSOR>(* Empty input for real rocq-ed CLI timeout experiments. *)
after:  1| <CURSOR>
```

The second reproducer uses **only real CLI requests**: stop the private process
while a first insertion is active, kill its client, and queue the timed-out
Delete during the documented 0.5-second escalation/restart window. The deletion
is applied after recovery. SIGSTOP merely makes that queueing window stable;
there is no fake request, preload hook, or changed production code.

**Practical exposure:** conditional but relevant to aggressive timeouts and
subsequent commands issued while a previous request is still cancelling or its
backend is restarting. Deterministic in the demonstrated queueing conditions;
not a claim that every timed-out Delete applies. Slow recovery/large startup
loads widen the opportunity; generous deadlines reduce it. Backward metadata-only
moves have the same publication structure. Ordinary long-running Rocq requests
have more opportunities for the watcher to run, explaining why the new looping
proof tests pass while this case does not.

**Required:** detect an already closed peer before executing a queued request,
and coordinate the initial disconnect check with publication. Preserve the
intended rule that a response failure **after** valid publication need not roll
back an already committed result. Add queued/pre-disconnected short-request tests,
not only active looping tactics and post-publication response failures.

### C2. [P2] One stalled interrupt connection blocks interruption and prevents shutdown

**Locations:** `rocq-ed/src/protocol.ml:291–318,322–359,465–467`.

The sole interrupt thread performs blocking `Marshal.from_channel` on each
accepted client. Its wake pipe is watched only by the outer accept loop, not
while reading the request. `finish_interrupt_server` writes the wake pipe and
unconditionally joins that thread. A peer that connects but does not finish
sending its control value blocks all later interrupt commands and blocks that
join. Final `Document.stop` cleanup has not yet run.

**Reproducer:** `stalled-interrupt-reader`. Connect to `interrupt.socket` and
leave the request unsent; run ordinary `rocq-ed interrupt`, then `rocq-ed stop`.

**Observed, three repetitions:**

```text
second interrupt exit=124; stop exit=0; server alive=True; backend alive=True
closing the stalled control peer releases shutdown
```

Thus Stop reports success and removes its session files while the server and
healthy backend are still alive indefinitely. Closing the original connection
lets both processes exit normally, confirming the blocked reader is the cause.

**Practical exposure:** low for an uninterrupted healthy CLI client, which sends
a tiny value immediately. Easy to reproduce with a paused/partial local control
client, or by opening the local socket. This is an availability/cleanup bug, not
an assertion of a remote attacker or untrusted-Marshal security boundary. The
existing malformed-client test closes its connection and therefore cannot find
this indefinitely open-input case.

**Required:** make control decoding deadline/wakeup-aware, or explicitly close
all owned active control connections during shutdown. A wakeup that is observed
only between connections is insufficient. Test stalled input as well as EOF and
malformed input.

### C3. [P1; surviving integration issue] Timing out the foreground server leaves busy Rocq work running

**Locations:** `ocaml-rocq-simple-api/bin/private-toplevel/main.ml:12–14`;
`rocq-ed/src/protocol.ml:448,501–614,679–690`.

The new disconnect watcher helps only while the daemon remains alive. Killing
the **foreground daemon itself** kills that watcher too. The private Rocq process
has its own session/process group, so GNU timeout's signal does not reach it.
There is no corresponding TERM/INT lifetime handler or parent-death mechanism to
terminate busy private work. Closing pipes cannot abort an infinite tactic that
never returns to protocol I/O.

**Reproducers:** `foreground-timeout` and `foreground-int-timeout`. Start
`rocq-ed init --no-daemon` under a three-second GNU timeout with `-k 0.2s`, wait
for readiness, and submit the infinite tactic from another client.

**Observed, three repetitions per signal:** timeout returns **124**, the server
is dead, its private process remains live and continues accumulating CPU ticks
in a different session/group, and the in-flight frontend receives EOF/error
**125**. TERM and INT both reproduce it. The diagnostics explicitly kill/reap
their own surviving processes afterward.

**Practical exposure:** easy and repeatable when a foreground server's lifetime
is managed with timeout, terminal signals, or a service supervisor that signals
only its original process/group, and a nonterminating computation is active.
An idle backend may exit on pipe EOF; do not generalize the persistent-orphan
observation to all idle shutdowns. `-k` and changing to INT do not fix the target
scope. Default daemon-mode frontend timeouts are different and now work in the
normal active-Rocq controls.

This consequence comes from the branch's added private `setsid`; the base source
had no such session creation in this path. Current group membership and surviving
CPU work were measured; the base binary was not rebuilt for an A/B comparison.

**Required:** define and implement ownership/lifetime cleanup across the new
session boundary, including foreground TERM/INT termination. Use appropriate
asynchronous cleanup or OS lifecycle supervision; do not assume that generic
process-group timeout signals include detached backends. Calling arbitrary
channel-manipulating APIs directly from a signal handler is not automatically safe.

### B1. [P1; old #6] Forked hard kill still depends on a responsive supervisor

**Locations:** `ocaml-rocq-simple-api/lib/api/rocq_toplevel.ml:113–130`;
`ocaml-rocq-simple-api/bin/private-toplevel/main.ml:340–350`.

The implementation is unchanged in the relevant respect: forked cleanup sends
`Supervisor_kill` rather than signalling the actual toplevel. A stalled
supervisor leaves the active request blocked on its response channel; closing
that channel can wait on the reader's lock forever.

**Reproducer:** `fork-kill-stopped-supervisor`. Run a looping tactic in a fork,
SIGSTOP its supervisor, then call API `kill`. A watchdog resumes the supervisor
after 0.3 seconds to keep the test bounded.

**Observed:** kill returns only after that external rescue (about **0.32 s**),
in all three repetitions. Without it kill does not complete. The retained
`fork-kill-idle-stopped-supervisor` variant demonstrates the idle path returning
success while its actual child remains running.

**Practical exposure:** a real independent-library/document-manager-materialize
failure mode, but **not currently a stock rocq-ed path**, since the CLI still
does not materialize/fork its backend. It additionally requires a stalled or
failed supervisor; a hard proof alone does not stall that supervisor.

**Required:** forced termination must not depend indefinitely on a responsive
helper. Preserve PID-reservation safety when implementing direct signalling or
acknowledged lifecycle handoff; merely marking the handle killed is insufficient.

### B2. [P2; old #9] Fork PID-pipe exhaustion still destroys the source

**Locations:** `ocaml-rocq-simple-api/bin/private-toplevel/main.ml:366–367,404–419,631–633`.

The PID-report pipe is still allocated outside the launcher's Unix-error handler.
The error escapes the request loop and terminates the source process, rather
than becoming an ordinary creation error.

**Reproducer:** `fork-pipe-failure`. Initialize a real source, lower only its
RLIMIT_NOFILE using `prlimit --pid <pid> --nofile=3:3`, and call public Fork.

**Observed, three repetitions:** private `Unix.EMFILE`, followed by API
`Interrupted (Failed End_of_file)` instead of `Error message` with a usable source.

**Practical exposure:** rare resource pressure in independent physical-fork
users. Stock rocq-ed does not use this operation. Normal sequential edits do
not cause this allocation; do not describe every session restart as taking this
Fork path.

**Required:** catch PID-pipe allocation errors and return the Fork creation-error
result while preserving the source. The separate startup-pipe leak was fixed;
that fix does not cover this allocation in the private process.

## Reproduced design/scope limitations, distinguished from implementation defects

### L1. [P2 design; old #10] API kill still cannot rescue a hung stop

**Locations:** `ocaml-rocq-simple-api/lib/api/rocq_toplevel.ml:113–130,236–248,304–307`.

Kill still waits in `Stopping`, while stop can wait forever in `waitpid`. Cleanup
ownership has already been claimed through `closed`, so changing only the state
branch is not sufficient to implement escalation safely.

**Reproducer:** `kill-during-stop`. SIGSTOP an idle direct child, start API stop,
then call API kill. A watchdog sends SIGCONT after 0.3 seconds.

**Observed, three repetitions:** kill waits for that external rescue and raises
`Stopped Normal`; without it both calls remain blocked. This is still specified
by the protocol state table, hence a design limitation rather than a newly
introduced discrepancy with that table.

**Exposure:** concurrent low-level stop/kill callers, not the ordinary CLI's
request pattern. If kill is intended as the unconditional escape hatch, implement
coordinated escalation and cleanup ownership. Otherwise document its exclusion
of a hung graceful shutdown.

### L2. [P2 scope] Disconnect cancellation does not cover blocking host-side I/O

**Locations:** `rocq-ed/src/protocol.ml:199–230,261–282`;
`rocq-ed/src/request.ml:401–408`; `rocq-doc-manager/lib/document.ml:710–729`.

The watcher can only interrupt/kill a registered **Rocq toplevel operation**.
For example, Commit performs its filesystem I/O in the server thread without
such an active operation. If it blocks, the watcher can mark the request
Cancelled but cannot stop it. After the grace period Document.kill continues
returning false, and the server never returns to accepting ordinary requests.

**Reproducer:** `commit-fifo`. Commit with `--force --file <FIFO>` to a FIFO
with no reader, kill the real frontend, wait beyond the grace period, then run
`interrupt --kill` and a timed Status.

**Observed, three repetitions:** interrupt returns **0**, saying `No request is
currently active.`, while Status times out **124** and the server remains stuck.
There are no preload hooks or backend SIGSTOPs in this case.

**Exposure:** uncommon with healthy local regular files; straightforward for a
FIFO target and relevant to stuck/slow network filesystem I/O. Long host-side
formatting or marshaling also lies outside a guarantee of promptly interrupting
all request work. This does not disprove the narrower public CLI promise to
interrupt a **Rocq operation**. It does disprove treating the new disconnect
watcher/0.5-second escalation as a universal deadline for arbitrary CLI requests.
Filesystem side effects are not transactionally reversed by metadata cloning.

**Required:** either state this scope explicitly, or isolate host-side work in a
cancellable worker/lifecycle design. Rejecting unsuitable file types can address
some cases but is not a universal filesystem deadline. Do not promise that a
queued Stop or `interrupt --kill` always rescues a blocked server.

## Current normal-use and timeout assessment

These are qualitative reachability estimates, not measured population failure
rates. Forced scheduling/fault conditions make executable evidence repeatable;
they do not imply those conditions occur on every edit.

| Situation | Current behavior / exposure |
| --- | --- |
| Ordinary active long tactic; frontend killed by GNU timeout TERM/INT | **Now works in controls:** disconnect causes cooperative cancellation, original logical document/proof state is restored, and the daemon remains usable. `-k`/GNU `--foreground` frontend variants also pass because EOF drives cancellation, not because their signal reaches Rocq. |
| Unresponsive private backend after frontend disconnect | **Now works in the tested direct-backend case:** after 0.5 s the server kills/restarts it and retains the original logical document. |
| `rocq-ed interrupt` / `interrupt --kill` during another request | **Now works in controls**, with ordinary client error 1, keep=successful progress preserved, proof still finishable, and restart after hard kill. C2 describes a control-connection availability exception. |
| Short mutation queued while earlier work/recovery exceeds its frontend deadline | **C1: can apply after timeout**, even when the client died before execution. Most practical with overlapping aggressive deadlines or slow recovery; not merely the unavoidable lost-reply ambiguity after publication. |
| Timeout of foreground `init --no-daemon` server itself | **C3: busy private work survives.** Direct signal delivery kills the daemon and its watcher, not the private session. |
| Timeout during initial daemon startup | Not comprehensively solved/tested here. Startup still precedes the ordinary request watcher. Default init detaches and is not a whole-session lifetime limit; partial startup can outlive its initial frontend. The report does not claim a forced slow-startup experiment. |
| Stalled local interrupt connection | **C2: later interruption and final shutdown can hang.** Easy with an open unsent request, rare for a healthy tiny complete control request. |
| Blocking host Commit I/O | **L2: no registered Rocq operation to kill**, so automatic cancellation is not an arbitrary host-request deadline. |
| Physical fork API failures | **B1/B2 remain outside stock rocq-ed**, despite the CLI now using other interruption APIs. |

**Operational conclusion:** the old blanket claim that frontend timeout leaves
all proof work running is obsolete. Conversely, exit 124 still is not a global
transaction/lifetime guarantee: C1, C3, and L2 remain counterexamples in different
phases/scopes. Do not blindly retry timed-out mutations. After valid publication,
a lost response can intentionally leave the result committed; C1 is specifically
a pre-execution closed-client failure, not a request to reverse that policy.

## Executable evidence

From the workspace root:

```sh
# Current backend matrix: fixed behaviors plus surviving old findings.
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/run.py --repeat 3

# Current real-CLI findings and positive controls.
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/rocq_ed_review.py --repeat 3
```

Both runners assert **correct behavior** and exit **1** on the current branch
because the documented findings/limitations remain. Individual names can be
passed instead of running the default matrix, for example:

```sh
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/rocq_ed_review.py queued-delete-during-recovery stalled-interrupt-reader
python3 fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests/interrupt_review/run.py fork-kill-stopped-supervisor fork-pipe-failure
```

Observed current results:

| Runner | Three-repetition result |
| --- | --- |
| Backend, 13 cases | **30 passes**, **9 intentional failures**: B1, B2, L1 each reproduced three times. |
| CLI, 13 cases | **21 positive-control passes**, **18 intentional failures**: C1 has two distinct reproducer cases, C2 one, C3 TERM/INT two, L2 one; each repeated three times. These are seven distinct findings/limitations overall, not 27 different bugs. |

The seven CLI controls cover frontend TERM, frontend INT, frontend GNU
`--foreground`, finite late-result handling, explicit cooperative interruption,
explicit hard interruption, and automatic hard escalation/restart. They verify
usable proof state, not just an empty text Status. The API controls retain the
real native startup, blocked-writer, descriptor-exhaustion, signal-window, and
publication-failure cases from the original review.

The FIFO inheritance hook now pauses **after actual open**, so it exercises the
atomic close-on-exec fix rather than waiting for the removed setter. BackTo is
checked through its **public API** under the new contract; the binary's historical
raw BackTo-Cancel probe is deliberately excluded from the current runner.

Linux `/proc`, Python 3, direnv, a C compiler, and util-linux `prlimit` are needed.
The CLI tests use a small **composed Dune fixture**, initialized with ordinary
dependency building, not `--no-build-deps`/`dune --root`. Queued/control tests use
real CLI clients and precisely described local socket/process conditions.
Backend race controls use the documented scheduling/fault hooks; no production
implementation is copied or substituted. Resource limits/signals are confined
to disposable test processes. Both runners become subreapers, bound their
observations, and clean up only their own test descendants, including detached
survivors. Tests are opt-in, not added as intentionally red default runtest rules.

## Existing tests, coverage, and validation limits

These composed-workspace commands pass, including the new supplied interruption
and transport tests:

```sh
direnv exec . dune build \
  @fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/all \
  @fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/install \
  @fmdeps/rocq-agent-toolkit/rocq-doc-manager/install \
  @fmdeps/rocq-agent-toolkit/rocq-ed/install
direnv exec . dune runtest --force \
  fmdeps/rocq-agent-toolkit/ocaml-rocq-simple-api/tests \
  fmdeps/rocq-agent-toolkit/rocq-doc-manager/tests \
  fmdeps/rocq-agent-toolkit/rocq-ed/tests
```

The supplied tests add useful coverage for real explicit interruption, keep
policies, replay after restart, disconnected clients, hard fallback, malformed
closed connections, and post-publication response failure. They do not cover
queued already-dead short mutations, indefinitely open control input, foreground
daemon lifetime signals, or blocked host Commit I/O. Backend tests still do not
cover the surviving supervisor and Fork allocation failures or stop escalation.

The remaining document-manager refactors were checked for locking, acknowledged
command bookkeeping, rollback-on-exception, clone/reference cleanup, restart,
and optional interrupt-as-error propagation. Dependency/OPAM and Dune changes are
consistent (`threads`, `mtime.clock.os`, and `mtime`); the extra Stop in the commit
test improves cleanup. No additional confirmed finding is claimed from those
changes. No full-workspace CI-equivalent build, statistical race-rate study, or
base-binary A/B timeout build was performed.
