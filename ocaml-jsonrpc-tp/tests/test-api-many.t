  $ yes 'echo [0,"Hello!"]' | head -n 100000 | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap | jsonrpc-tp.test-service 4 | jsonrpc-tp.tp_unwrap | wc -l
  200000
