  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ eval $(rocq-ed init --no-build-deps test.v)
  $ data_dir="$HOME/.cache/rocq-ed/$ROCQED_SESSION_ID"
  $ server_pid=$(cat "$data_dir/pid")

Interrupting an idle session is a harmless no-op.

  $ rocq-ed interrupt
  No request is currently active.
  $ rocq-ed interrupt --kill
  No request is currently active.

A cooperative explicit interrupt reports an ordinary request error, applies
--keep=successful, and leaves the session usable.

  $ rocq-ed insert --text $'Goal True.\nProof.\n'
  $ rocq-ed insert --keep=successful --text $'idtac.\nlet rec loop := loop in loop.\nexact I.' > cooperative.out 2>&1 &
  $ client_pid=$!
  $ until grep -q 'let rec loop' "$data_dir/log"; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt
  Interruption requested.
  $ wait "$client_pid"
  [1]
  $ grep 'User interrupt' cooperative.out
  User interrupt.
  $ rocq-ed status --context-lines=all
     1| Goal True.
     2| Proof.
     3| idtac.
     4| <CURSOR>
  $ rocq-ed insert --text $'exact I.\nQed.\n'

A hard explicit interrupt kills and restarts the backend while preserving the
logical document and returning a normal request error to the waiting client.
A command that will block during replay is first added to the processed prefix.

  $ mkfifo replay-block.out
  $ exec 3<> replay-block.out
  $ rocq-ed insert --feedback=none --text 'Redirect "replay-block" Check I.'
  $ rocq-ed insert --text $'\nGoal True.\nProof.\n'
  $ loop_requests=$(grep -c 'Request.*let rec loop' "$data_dir/log")
  $ rocq-ed insert --text 'let rec loop := loop in loop.' > hard.out 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -c 'Request.*let rec loop' "$data_dir/log")" -gt "$loop_requests" ]; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt --kill
  Hard interruption requested.
  $ wait "$client_pid"
  [1]
  $ grep 'User interrupt (hard kill)' hard.out
  User interrupt (hard kill).
  $ exec 3>&-

A text status request reports an interruption while obtaining its optional
goals instead of silently succeeding with empty output.

  $ status_requests=$(grep -c 'Request \[Status' "$data_dir/log" || true)
  $ rocq-ed status --goals > status.out 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -c 'Request \[Status' "$data_dir/log" || true)" -gt "$status_requests" ]; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt
  Interruption requested.
  $ wait "$client_pid"
  [1]
  $ grep 'User interrupt' status.out
  Error: User interrupt.

The restarted backend replays the processed prefix. That replay is itself
interruptible, and only acknowledged commands remain in its bookkeeping.

  $ goal_requests=$(grep -c 'Request \[Goals\]' "$data_dir/log" || true)
  $ rocq-ed goals > replay.out 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -c 'Request \[Goals\]' "$data_dir/log" || true)" -gt "$goal_requests" ]; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt
  Interruption requested.
  $ wait "$client_pid"
  [1]
  $ grep 'User interrupt' replay.out
  Error: User interrupt.
  $ exec 3<> replay-block.out
  $ timeout 10 rocq-ed goals
  Goal 1:
    ============================
    True
  $ exec 3>&-
  $ rm replay-block.out
  $ rocq-ed insert --text $'exact I.\nQed.\n'

Return to an empty document and check that an interrupted forward move stops
before the active sentence without ending the session.

  $ rocq-ed move --item=-all
  $ rocq-ed delete --count-items=all
  $ loop_requests=$(grep -c 'Request.*let rec loop' "$data_dir/log")
  $ rocq-ed insert --keep=all --text $'Goal True.\nProof.\nlet rec loop := loop in loop.\nexact I.\nQed.' > keep-all.out 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -c 'Request.*let rec loop' "$data_dir/log")" -gt "$loop_requests" ]; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt
  Interruption requested.
  $ wait "$client_pid"
  [1]
  $ move_requests=$(grep -c 'Request \[Move' "$data_dir/log" || true)
  $ rocq-ed move --item=+all > move.out 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -c 'Request \[Move' "$data_dir/log" || true)" -gt "$move_requests" ]; do sleep 0.05; done
  $ sleep 0.1
  $ rocq-ed interrupt
  Interruption requested.
  $ wait "$client_pid"
  [1]
  $ grep 'User interrupt' move.out
  User interrupt.
  $ rocq-ed status --context-lines=all
     1| Goal True.
     2| Proof.
     3| <CURSOR>let rec loop := loop in loop.
     4| exact I.
     5| Qed.
  $ rocq-ed move --item=-all
  $ rocq-ed delete --count-items=all

Killing a client cancels its active request. Partial document changes are
not published, and the server remains available without opening the FIFO.

  $ mkfifo block.out
  $ rocq-ed insert --keep=all --text $'Definition partial := 0.\nRedirect "block" Check I.' > /dev/null 2>&1 &
  $ client_pid=$!
  $ until grep -q 'Redirect.*block' "$data_dir/log"; do sleep 0.05; done
  $ sleep 0.1
  $ kill -KILL "$client_pid"
  $ wait "$client_pid" > /dev/null 2>&1 || true
  $ timeout 10 rocq-ed status
     1| <CURSOR>
  $ kill -0 "$server_pid"
  $ rm block.out

A catchable client signal also cancels the request without killing the server.

  $ mkfifo sigint.out
  $ (trap - INT; exec rocq-ed insert --keep=none --text 'Redirect "sigint" Check I.' > /dev/null 2>&1) &
  $ client_pid=$!
  $ until grep -q 'Redirect.*sigint' "$data_dir/log"; do sleep 0.05; done
  $ sleep 0.1
  $ kill -INT "$client_pid"
  $ wait "$client_pid"
  [130]
  $ timeout 10 rocq-ed status
     1| <CURSOR>
  $ kill -0 "$server_pid"
  $ rm sigint.out

If cooperative interruption does not complete within the grace period, the
server kills and restarts the Rocq backend.

  $ mkfifo hard-block.out
  $ rocq-ed insert --keep=none --text 'Redirect "hard-block" Check I.' > /dev/null 2>&1 &
  $ client_pid=$!
  $ until grep -q 'Redirect.*hard-block' "$data_dir/log"; do sleep 0.05; done
  $ sleep 0.1
  $ top_pid=$(ps -o pid= --ppid "$server_pid" | awk 'NR == 1 {print $1}')
  $ kill -STOP -- "-$top_pid"
  $ kill -KILL "$client_pid"
  $ wait "$client_pid" > /dev/null 2>&1 || true
  $ timeout 10 rocq-ed status
     1| <CURSOR>
  $ kill -0 "$server_pid"
  $ rm hard-block.out

Malformed requests are confined to their connection and do not stop the
server.

  $ python3 - "$data_dir" <<'PY'
  > import os
  > import socket
  > import sys
  > os.chdir(sys.argv[1])
  > client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
  > client.connect("socket")
  > client.sendall(b"not an OCaml Marshal value")
  > client.close()
  > PY
  $ timeout 10 rocq-ed status
     1| <CURSOR>
  $ kill -0 "$server_pid"

A response-write failure after publication is logged without stopping the
server or rolling back the published request.

  $ python3 - <<'PY' | rocq-ed insert
  > import sys
  > sys.stdout.write(" " * 8_000_000)
  > PY
  $ large_requests=$(grep -Fc 'Request [Insert({text = " ";' "$data_dir/log" || true)
  $ sending_responses=$(grep -c 'Sending response' "$data_dir/log" || true)
  $ response_failures=$(grep -c 'Response could not be delivered' "$data_dir/log" || true)
  $ rocq-ed insert --print-context=all --text ' ' > /dev/null 2>&1 &
  $ client_pid=$!
  $ until [ "$(grep -Fc 'Request [Insert({text = " ";' "$data_dir/log" || true)" -gt "$large_requests" ]; do sleep 0.01; done
  $ kill -STOP "$client_pid"
  $ until [ "$(grep -c 'Sending response' "$data_dir/log" || true)" -gt "$sending_responses" ]; do sleep 0.01; done
  $ kill -KILL "$client_pid"
  $ wait "$client_pid" > /dev/null 2>&1 || true
  $ until [ "$(grep -c 'Response could not be delivered' "$data_dir/log" || true)" -gt "$response_failures" ]; do sleep 0.01; done
  $ rocq-ed commit
  $ wc -c < test.v
  8000001
  $ timeout 10 rocq-ed goals
  Not currently in a proof.
  $ kill -0 "$server_pid"

A control client that connects without sending a request does not block later
interruptions or final shutdown.

  $ python3 - "$data_dir" <<'PY' &
  > import os
  > import pathlib
  > import socket
  > import sys
  > data = pathlib.Path(sys.argv[1]).resolve()
  > os.chdir(data)
  > client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
  > client.connect("interrupt.socket")
  > pathlib.Path("stalled-control-ready").touch()
  > client.recv(1)
  > PY
  $ control_pid=$!
  $ for _ in $(seq 1 500); do [ -e "$data_dir/stalled-control-ready" ] && break; sleep 0.01; done
  $ test -e "$data_dir/stalled-control-ready"
  $ rocq-ed interrupt
  No request is currently active.
  $ rm "$data_dir/stalled-control-ready"
  $ rocq-ed stop
  $ wait "$control_pid"
  $ for _ in $(seq 1 500); do kill -0 "$server_pid" 2> /dev/null || break; sleep 0.01; done
  $ kill -0 "$server_pid" 2> /dev/null
  [1]
