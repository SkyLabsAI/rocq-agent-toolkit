  $ cat > calls.txt <<EOF
  > echo [2,"Bye!"]
  > echo [3,"Coucou!"]
  > echo [1,"Hello!"]
  > echo [0,"First!"]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap | jsonrpc-tp.delayed-echo-service 4 | jsonrpc-tp.tp_unwrap
  { "method": "done_sleeping", "jsonrpc": "2.0" }
  { "id": 4, "jsonrpc": "2.0", "result": "First!" }
  { "method": "done_sleeping", "jsonrpc": "2.0" }
  { "id": 3, "jsonrpc": "2.0", "result": "Hello!" }
  { "method": "done_sleeping", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": "Bye!" }
  { "method": "done_sleeping", "jsonrpc": "2.0" }
  { "id": 2, "jsonrpc": "2.0", "result": "Coucou!" }
