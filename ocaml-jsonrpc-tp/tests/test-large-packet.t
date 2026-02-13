  $ cat > calls.txt <<EOF
  > yes [1000000]
  > yes [2000000]
  > yes [4000000]
  > yes [8000000]
  > EOF

Testing the sequential API.

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap | jsonrpc-tp.test-api | jsonrpc-tp.tp_unwrap | perl -pe 's/(y+)/"yx" . length($1)/ge'
  { "method": "readyx1_seq", "jsonrpc": "2.0" }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 1,
    "jsonrpc": "2.0",
    "result": "yx1000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": "yx2000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "result": "yx4000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": "yx8000000"
  }

Testing the parallel API.

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap | jsonrpc-tp.test-api 1 | jsonrpc-tp.tp_unwrap | perl -pe 's/(y+)/"yx" . length($1)/ge'
  { "method": "readyx1", "jsonrpc": "2.0" }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 1,
    "jsonrpc": "2.0",
    "result": "yx1000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": "yx2000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "result": "yx4000000"
  }
  { "method": "big_string", "jsonrpc": "2.0" }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": "yx8000000"
  }
