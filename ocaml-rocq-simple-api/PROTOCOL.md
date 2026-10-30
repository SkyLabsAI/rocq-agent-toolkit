Internal Toplevel Protocol
==========================

This file describes the communication protocol used between the implementation
of the public `Rocq_toplevel` module (see `lib/api/rocq_toplevel.mli`) and the
private top-level processes (implemented by `bin/private-toplevel/main.ml`).

## Terminology

- **Parent**: OCaml process using the public `Rocq_toplevel` API.
- **Child**: one `rocq-simple-api.private.toplevel` process.
- **Command stream**: parent-to-child requests and completion decisions.
- **Response stream**: child-to-parent startup, response, and acknowledgement
  messages.
- **Request ID**: a monotonically increasing integer local to one
  `Rocq_toplevel.toplevel` handle.
- **State ID** (`sid`): Rocq's integer state identifier after a command or
  rollback.

Only one ordinary operation may run at a time on a given top-level. The public
`interrupt` and `kill` operations, as well as immutable queries such as
`get_pid`, may run concurrently with it.

## Compatibility and trust boundary

All protocol values are serialized with OCaml `Marshal`.

Consequently:

- the protocol is not stable across incompatible changes to the OCaml types;
- parent and child must use matching binaries and libraries;
- this is not a protocol for untrusted peers, since unmarshalling attacker
  controlled data is unsafe; and
- stdin and stdout of the private process are reserved exclusively for
  protocol messages.

Protocol constructors are declared in
`lib/internal/rocq_toplevel_data.ml`.

## Transport

Each top-level uses two logical streams:

```text
parent                                      private top-level

command output  --------------------------> stdin
response input  <-------------------------- stdout
```

Initial top-levels use two anonymous pipes. Forked top-levels use three named
FIFOs because the API parent cannot directly pass new descriptors to a process
forked by a private top-level. Two carry the command and response streams; the
third is a lifecycle channel to a supervisor process. All descriptors are
close-on-exec unless intentionally installed as protocol descriptors.

Every marshalled value is flushed before the sender performs the next protocol
step. The protocol relies on this ordering: `Cancel` is flushed before
`SIGINT`, and `Cancel_signal_sent` is flushed after the signal call returns.

Parent-side writes and output-channel closes block `SIGPIPE` in the calling
thread. A newly pending `SIGPIPE` is consumed before the previous signal mask
is restored, so a closed peer is reported as an OCaml transport exception and
can never terminate the API host process.

The private process inherits stderr from its parent. Diagnostic output may be
written there, but never to stdout.

## Process startup

### Initial top-level

`Rocq_toplevel.init` performs the following steps:

1. Create the command and response pipes.
2. Start `rocq-simple-api.private.toplevel` with the command pipe as stdin and
   the response pipe as stdout.
3. Wait for the startup message on the response pipe:

   ```ocaml
   (pid, sid) : int * int
   ```

4. Check that the reported PID is the PID returned by
   `Unix.create_process_env`.

Raw descriptors are tracked as owned resources until they are closed or
transferred into channels. Startup cleanup therefore closes each descriptor
exactly once, including when allocation of the second pipe fails.

Before initializing Rocq, the private executable calls `setsid`, making its
PID both the session ID and process-group ID, and blocks `SIGINT`.

The startup message is sent only after Rocq initialization has completed.

### Process groups

Each independently addressable private top-level is a process-group leader.
Cooperative interruption uses:

```ocaml
Unix.kill (-pid) Sys.sigint
```

This signals the private process together with sentence-splitter children and
other workers in its process group, without signalling the parent API process.

`kill` similarly sends `SIGKILL` to the process group and, defensively, to the
immediate PID.

## Protocol types

### Commands

The command GADT associates each command with its result and error types:

```ocaml
type (_, _) cmd =
  | Run : {
      loc : Loc.t;
      text : string;
    } -> (run_data, string * run_error) cmd

  | BackTo : {
      sid : int;
    } -> (unit, string) cmd

  | Fork : {
      pipe_in : string;
      pipe_out : string;
      pipe_supervisor : string;
    } -> (int, string) cmd

  | StructuredGoals :
      (structured_goal list option, empty) cmd

  | LocAfterBlanks : {
      loc : Loc.t;
      text : string;
    } -> (Loc.t, string) cmd

  | Split : {
      loc : Loc.t;
      text : string;
      sid : int option;
    } -> (raw_split_data, empty) cmd
```

`BackTo` is the only uninterruptible command. Rocq does not retain enough
state to restore the pre-backtrack state reliably, so the parent never
publishes cooperative cancellation for it and the child keeps `SIGINT`
blocked while it executes. Unconditional `kill` and fatal transport failures
still terminate an active `BackTo` request.

The parent wraps each command in a request ID:

```ocaml
type ('result, 'error) request = {
  request_id : int;
  command : ('result, 'error) cmd;
}
```

### Response messages

For every accepted request, the child first sends `Started` and later sends
one terminal `Finished` message:

```ocaml
type ('result, 'error) response =
  | Completed of {
      request_id : int;
      sid : int;
      result : ('result, 'error) Result.t;
    }
  | Interrupted of {
      request_id : int;
      sid : int;
    }

type ('result, 'error) message =
  | Started of int
  | Finished of ('result, 'error) response
```

`Completed` includes both successful results and ordinary command errors.
`Interrupted` is reserved for operation interruption. Cooperative
interruption is exposed as
`Rocq_toplevel.Interrupted Rocq_toplevel.Interrupt`.

### Completion decisions

After every terminal response, the child waits on the command stream for
exactly one decision for that request:

```ocaml
type control =
  | Continue of int
  | Cancel of int
  | Cancel_signal_sent of int

type control_ack =
  | Cancel_ack of {
      request_id : int;
      sid : int;
    }

type supervisor_control =
  | Supervisor_stop
  | Supervisor_kill
```

A normal request receives `Continue`. A request for which interruption won the
parent-side race receives `Cancel`, followed by `Cancel_signal_sent` after the
parent has issued `SIGINT`, and produces exactly one `Cancel_ack` on the
response stream.

All IDs must match the active request. A duplicate, stale, or mismatched ID
is a protocol error.

## Normal request sequence

A normal operation follows this sequence:

```text
parent                                      child

Request { id; command }  ----------------->
                         <-----------------  Started id
                                             execute command
                         <-----------------  Finished (Completed {
                                                id; sid; result
                                              })
Continue id              ----------------->
                                             accept next request
```

Detailed steps:

1. The parent atomically changes its state from `Idle` to
   `Reserving {interruptible; cancel_pending = false}`. `interruptible` is
   false exactly for `BackTo`.
2. The request thread allocates the next request ID and changes the state to
   `Preparing {request_id = id; interruptible; cancel_pending}`. Reserving
   before allocation ensures IDs are monotonic in command-stream order.
3. The parent writes and flushes the request.
4. The child decodes the complete request while `SIGINT` is blocked.
5. The child writes and flushes `Started id`.
6. The child installs its exception/cleanup boundary and unblocks `SIGINT`
   only when the command is interruptible.
7. The child executes the command.
8. The child blocks `SIGINT` before writing the terminal response.
9. The child writes and flushes `Finished (Completed ...)`.
10. The child waits for a decision instead of decoding another request.
11. The parent atomically changes
    `Running {request_id = id; interruptible}` to
    `Completing {request_id = id}`. This is the completion linearization
    point.
12. The parent writes and flushes `Continue id`, records the response state
    ID, and changes its state back to `Idle`.
13. The child receives `Continue id` and returns to command decoding.

An ordinary Rocq error still follows this sequence. It appears as:

```ocaml
Completed { result = Error error; ... }
```

and does not use the interruption path.

## Cooperative interruption

### Interruption during `Reserving` or `Preparing`

The parent must never send `SIGINT` before `Started`, because an asynchronous
exception during `Marshal.from_channel` could leave the main stream between
messages.

If `interrupt` observes an interruptible request in `Reserving` or
`Preparing`, it sets `cancel_pending = true` and returns. The request thread
preserves the flag when it publishes the request ID. After it receives
`Started id`, it enters `Cancelling`, publishes the cancellation, and then
enters `Interrupting {request_id = id}`. For an uninterruptible request,
`interrupt` does nothing and never latches cancellation.

### Interruption during execution

The active interruption sequence is:

```text
parent                                      child

                         <-----------------  Started id
Cancel id                ----------------->
SIGINT to process group  ----------------->
Cancel_signal_sent id    ----------------->
                                             catch interruption
                                             restore pre-command state
                         <-----------------  Finished (Interrupted {
                                                id; sid
                                              })
                         <-----------------  Cancel_ack { id; sid }
parent raises Rocq_toplevel.Interrupted Rocq_toplevel.Interrupt
```

The parent always writes and flushes `Cancel id` before sending `SIGINT`, then
writes and flushes `Cancel_signal_sent id` after the signal system call has
returned. The latter is a signal-delivery fence: once the child reads it, the
cancellation signal has either been consumed by command execution or is
pending while blocked.

On interruption, the child:

1. blocks `SIGINT` again;
2. restores the state that existed before the command;
3. writes and flushes `Finished (Interrupted ...)`;
4. reads the matching `Cancel id` and `Cancel_signal_sent id` records;
5. removes `SIGINT` with `sigwait` if it is still pending;
6. writes and flushes `Cancel_ack` with the restored state ID; and
7. only then accepts another request.

The parent consumes both the terminal response and the acknowledgement
before changing the state to `Idle` and raising
`Rocq_toplevel.Interrupted Rocq_toplevel.Interrupt`.

### Commands that consume `Sys.Break`

Rocq or a plugin may catch `Sys.Break` and return an ordinary command error or
result. The child therefore does not assume that a completed execution leaves
`SIGINT` pending. After reading `Cancel_signal_sent`, it checks `sigpending`
and calls `sigwait` only when the signal is present. The completed result is
discarded, the pre-command state is restored, and cancellation still wins.

## Completion/interruption race

Completion and interruption race on the parent-side state:

```text
Running {request_id = id; interruptible = true}
  -> Completing {request_id = id}
Running {request_id = id; interruptible = true}
  -> Cancelling {request_id = id}
```

Only one atomic transition can win. `Cancelling` covers the short interval in
which `Cancel` and `SIGINT` are being published. It then changes to
`Interrupting`.

### Completion wins

If the request thread changes `Running` to `Completing` first:

- `interrupt` observes `Completing` and does nothing;
- the parent sends `Continue`;
- the completed result is returned; and
- no cancellation signal is sent.

### Interruption wins after the child computed a result

The child may already have blocked `SIGINT` and sent `Completed` when the
interrupting thread wins. The child is still waiting for its completion
decision, so the parent can safely send `Cancel` rather than `Continue`:

```text
parent                                      child

                         <-----------------  Finished (Completed {
                                                id; sid_after; result
                                              })
Cancel id                ----------------->
SIGINT to process group  ----------------->
Cancel_signal_sent id    ----------------->
                                             drain SIGINT if still pending
                                             clean up resources
                                             restore pre-command state
                         <-----------------  Cancel_ack { id; sid_before }
parent discards result and raises Interrupted Interrupt
```

After the signal fence, the child uses `Unix.sigpending` and, when necessary,
`Unix.sigwait` while `SIGINT` is blocked. This drains a pending signal without
waiting when command execution already consumed it.

In this case, the `sid` in the earlier `Completed` response is no longer
current. The `sid` in `Cancel_ack` is authoritative, and the parent records
that value before returning to `Idle`.

The mandatory post-response `Continue`/`Cancel` decision is what closes this
race. Polling for cancellation or issuing a later no-op synchronization
command would not provide the same ordering guarantee.

## Parent state

The public API tracks this atomic state:

```ocaml
type stopped_reason =
  | Normal
  | Killed
  | Failed of exn

type interrupted_reason =
  | Interrupt
  | Killed
  | Failed of exn

type state =
  | Idle
  | Reserving of {
      interruptible : bool;
      cancel_pending : bool;
    }
  | Preparing of {
      request_id : int;
      interruptible : bool;
      cancel_pending : bool;
    }
  | Running of {request_id : int; interruptible : bool}
  | Completing of {request_id : int}
  | Cancelling of {request_id : int}
  | Interrupting of {request_id : int}
  | Stopping
  | Killing
  | Failing of {error : exn}
  | Terminated of {reason : stopped_reason}
```

Typical transitions are:

```text
Idle
  -> Reserving {interruptible = i; cancel_pending = false}
  -> Preparing {
       request_id = id; interruptible = i; cancel_pending = false
     }
  -> Running {request_id = id; interruptible = i}
  -> Completing {request_id = id}
  -> Idle

Idle
  -> Reserving {interruptible = true; cancel_pending = false}
  -> Reserving {interruptible = true; cancel_pending = true}
  -> Preparing {
       request_id = id; interruptible = true; cancel_pending = true
     }
  -> Cancelling {request_id = id}
  -> Interrupting {request_id = id}
  -> Idle

Running {request_id = id; interruptible = true}
  -> Cancelling {request_id = id}
  -> Interrupting {request_id = id}
  -> Idle

Idle or active state
  -> Killing
  -> Terminated {reason = Killed}

Active state
  -> Failing {error}
  -> Terminated {reason = Failed error}

Idle
  -> Stopping
  -> Terminated {reason = Normal}
```

`interrupt` behavior by state:

- `Idle` or `Completing`: do nothing;
- an uninterruptible `Reserving`, `Preparing`, or `Running`: do nothing;
- an interruptible `Reserving` or `Preparing`: latch cancellation, but do not
  signal;
- an interruptible `Running`: enter `Cancelling`, publish `Cancel` and
  `SIGINT`, and enter `Interrupting`;
- `Cancelling` or `Interrupting`: do nothing because interruption is pending;
- `Stopping`, `Killing`, or `Failing`: wait for termination, then raise the
  matching `Rocq_toplevel.Stopped` exception;
- `Terminated`: raise the matching `Rocq_toplevel.Stopped` exception.

A second ordinary operation on a top-level with an active request raises
`Rocq_toplevel.Busy`. `stop` and `StateID.current` do the same. Ordinary
operations remain serial even though `interrupt` and `kill` may run
concurrently with one.

## Signal masking

The private process blocks `SIGINT` before Rocq initialization. Workers
created during initialization therefore inherit the blocked mask.

For each request, the main private thread:

1. decodes the request with `SIGINT` blocked;
2. sends `Started` with `SIGINT` blocked;
3. unblocks `SIGINT` only for interruptible command execution, keeping it
   blocked throughout `BackTo`;
4. blocks it again before sending `Finished`; and
5. keeps it blocked while waiting for `Continue` or `Cancel`.

This protects both Marshal streams from asynchronous exceptions. The
post-signal fence lets the child determine whether a cancellation that lost
the execution race remains pending or was consumed by command execution.

## Command rollback and cleanup

Cancellation restores the Rocq state that existed before the command. Commands
also have command-specific cleanup obligations:

- **`Run`**: restore the pre-command state. Filesystem or other external side
  effects are not transactionally reversed.
- **`BackTo`**: never accepts cooperative cancellation because its
  pre-command state cannot be restored reliably.
- **`LocAfterBlanks`**: restore the global lexer state with `Fun.protect`.
- **`StructuredGoals`**: no Rocq-state mutation is expected.
- **`Split`**: terminate and synchronously reap the sentence-splitter child.
- **`Fork`**: terminate a partially or fully created forked top-level if
  cancellation wins.

The command-specific cleanup for a completed `Fork` is necessary because
cancellation may win after the child PID has already been computed. A failed
Rocq-state rollback is a fatal protocol failure; the child never acknowledges
cancellation with a state ID that it could not actually restore.

## Fork protocol

`Rocq_toplevel.fork` creates a new independently addressable private top-level
that starts at the source top-level's current state.

The API parent first creates a temporary directory containing:

- `in`: a FIFO that becomes the forked child's stdin;
- `out`: a FIFO that becomes the forked child's stdout; and
- `supervisor`: a FIFO used to release or kill the forked process.

It opens temporary read-write guards on all FIFOs with `O_CLOEXEC` in the
atomic `open` operation and keeps a dedicated writer open on `supervisor`.
It then sends:

```ocaml
Fork {pipe_in; pipe_out; pipe_supervisor}
```

The private source process blocks `SIGINT` while it launches a detached
supervisor using the double-fork pattern. The short-lived launcher is reaped
synchronously by the source. The supervisor calls `setsid`, forks the actual
private top-level, reports its PID to the source over a private pipe, and then
waits on the supervisor FIFO.

In the actual forked top-level:

1. call `setsid` to establish its own session and process group;
2. open and install the command and response FIFO descriptors; and
3. restart the protocol loop, beginning with the usual `(pid, sid)` startup
   message.

The supervisor deliberately does not reap the actual top-level while the API
keeps the supervisor FIFO open. Therefore an unexpectedly exited top-level
remains a zombie with a reserved PID, and owner-side signalling can never hit
a reused PID. On `Supervisor_stop`, the supervisor waits for normal exit. On
`Supervisor_kill`, or unexpected FIFO EOF, it kills the top-level process
group and PID before waiting. The detached supervisor is then reaped by the
operating system's child reaper.

The source returns the actual top-level PID as the result of `Fork`. The API
parent opens the command and response FIFOs, waits up to ten seconds for the
startup message, closes the temporary guards, removes the FIFO paths,
validates the startup PID, and constructs the new `toplevel` handle while
retaining the supervisor writer.

Forked handles retain the source handle's internal top-level identity so state
identifiers for their shared history remain valid on the fork. Their request
IDs, channels, process groups, supervisors, and states are independent. In
particular, stopping or killing the source does not terminate the supervisor
or the forked top-level.

## Sentence splitting

`Split` executes parsing in a short-lived child process so parser-side effects
cannot corrupt the main private top-level.

The private top-level blocks `SIGINT` before creating the result pipe and
keeps it blocked across `fork`. The parent restores its previous mask only
after installing cleanup that owns the child PID and result channel. The
child restores the mask only after installing an exit-on-exception boundary
and disconnecting all inherited protocol descriptors.

The splitter child:

- remains in the owning top-level's process group;
- redirects stdin, stdout, and stderr to `/dev/null`;
- marshals its result through a private pipe; and
- exits.

On cancellation, process-group `SIGINT` reaches both the private top-level and
the splitter. The private top-level closes the result channel, kills the child
if necessary, calls `waitpid`, and reports interruption. The signal cannot
escape into either process before those cleanup boundaries are active.

## Unconditional kill

`Rocq_toplevel.kill` applies to the whole top-level rather than one request.
It eventually changes any live `Idle` or active state to `Killing`, even when
a racing request reaches `Idle` before `kill` performs its first atomic
transition.

If cancellation publication is in `Cancelling`, `kill` waits for publication
to finish before changing the state. This prevents a delayed `SIGINT` from
being sent after the process has already been killed and reaped.

Once `Killing` wins, `kill`:

1. for an initial top-level, sends `SIGKILL` to the process group and PID; for
   a forked top-level, sends `Supervisor_kill` to its supervisor;
2. closes the command and response streams;
3. closes the supervisor stream when present;
4. calls `waitpid` for an initial direct child;
5. records `Terminated {reason = Killed}`; and
6. returns.

An operation for which `Killing` wins raises
`Rocq_toplevel.Interrupted Rocq_toplevel.Killed`. If the operation reaches
`Idle` first, it may return normally or raise
`Rocq_toplevel.Interrupted Rocq_toplevel.Interrupt`; `kill` then transitions
that top-level from `Idle` to `Killing` anyway.

After `kill`, ordinary operations, `stop`, and later calls to `kill` raise
`Rocq_toplevel.Stopped Rocq_toplevel.Killed`. No later `stop` call is required
for cleanup.

For a forked top-level, the API is not the operating-system parent and does
not call `waitpid`. Its supervisor owns process termination and reaping, and
keeps the PID reserved until owner-side cleanup is published.

## Normal stop and EOF

`Rocq_toplevel.stop` is permitted when the state is `Idle`. If a request is
active, it raises `Rocq_toplevel.Busy`. Otherwise it enters `Stopping`, closes
the command and response streams, and sends `Supervisor_stop` when applicable.
The private command loop observes EOF on stdin and exits. The API reaps an
initial direct child; a fork supervisor waits for and reaps its child. The API
then records `Terminated {reason = Normal}`.

Later operations and repeated calls to `stop` raise
`Rocq_toplevel.Stopped Rocq_toplevel.Normal`.

Unexpected EOF, malformed messages, mismatched IDs, or other transport
failures make the handle unusable. The API enters `Failing {error}`, kills the
process group, performs the same owner-side cleanup, and records
`Terminated {reason = Failed error}`. The active operation raises
`Rocq_toplevel.Interrupted (Rocq_toplevel.Failed error)`. Later operations
raise `Rocq_toplevel.Stopped (Rocq_toplevel.Failed error)`.

## Protocol invariants

Implementations must preserve all of the following:

1. At most one main request is active on a top-level; another ordinary
   operation raises `Busy`.
2. Every request has one request ID used on both streams.
3. The child sends exactly one `Started` before executing a request.
4. The child sends exactly one terminal `Finished` response.
5. The child decodes no later request until it receives `Continue` or
   `Cancel`.
6. The parent flushes `Cancel` before sending `SIGINT`, and flushes the
   matching `Cancel_signal_sent` fence after the signal system call returns.
7. Without `kill` or transport failure, every `Cancel` produces exactly one
   matching `Cancel_ack`.
8. A parent that sent `Cancel` waits for `Cancel_ack` before returning to
   `Idle`.
9. The acknowledgement state ID is authoritative after cancellation.
10. Accepted request IDs are monotonic in command-stream order.
11. `kill` performs all owner-side cleanup before returning.
12. Once called on a live top-level, `kill` leaves it terminated even if a
    racing operation reaches `Idle` first.
13. `SIGINT` is blocked during Marshal decoding and encoding.
14. No stale signal may remain pending when the next command begins.
15. Request and decision writes on the command stream never overlap.
16. Helper processes must not read stdin or write stdout inherited from the
    private top-level.
17. A supervisor keeps a forked top-level's PID reserved until owner-side
    cleanup and remains independent from the source top-level.
18. The process that forks a child remains responsible for reaping it.
19. A fatal failure cause is retained in the active `Interrupted` and later
    `Stopped` exceptions.
20. `BackTo` never transitions to `Cancelling` or receives `Cancel`; calls to
    `interrupt` while it is active are no-ops.
21. A broken parent-side transport write raises an OCaml exception without
    delivering fatal `SIGPIPE` to the API host.
22. Every raw startup descriptor has exactly one cleanup owner.
23. `SIGINT` is blocked across splitter pipe creation and `fork` until both
    resulting processes have installed their respective cleanup boundaries.
24. FIFO guards are atomically close-on-exec.
25. A rollback failure is fatal and never produces `Cancel_ack`.
