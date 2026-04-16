Basic cram test for session operations

  $ cat > basic.v <<EOF
  > (* Simple test file *)
  > EOF

  $ rocq-session-cram-test basic.v \
  > "cursor" \
  > '["insert", {"text": "Definition test_val := 42."}]' \
  > "cursor"
  cursor({})
  = {"status": "ok", "index": 0}
  insert({"text": "Definition test_val := 42."})
  = {"status": "ok", "index": 1, "command_data": {"synterp_ast": {"attrs": {"id": "", "kind": "Definition", "proof": false}, "pure": true, "controls": [], "kind": "Definition"}, "proof_state": null, "feedback_messages": [{"text": "test_val is defined", "quickfix": [], "loc": null, "level": "info"}], "globrefs_diff": {"removed_inductives": [], "added_inductives": [], "removed_constants": [], "added_constants": ["basic.test_val"]}}}
  cursor({})
  = {"status": "ok", "index": 1}