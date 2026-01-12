Rocq Document Manager
=====================

This utility can be used to programmatically edit a Rocq source file.

Usage Summary
-------------

The document manager can be started by running with the following command.
```sh
rocq-doc-manager [ROCQ_ARGS] FILE
```
In effect, the document manager expects the same command-line arguments as the
`rocq compile` command does.

Once the document manager is running, it can be interacted with using JSON-RPC
2.0 requests wrapped in a simple transfer protocol layer. The document manager
waits for request packages on its `stdin`, and sends the corresponding replies
to its `stdout`. Request are handled sequentially, and in order.

**Note**: `rocq-doc-manager` expects dependencies of the `FILE` to be built.

Transfer Protocol
-----------------

Packets sent to / received from the document manager have the following shape.
```
Content-Length: <size>\r\n\r\n<data>
```
The data part is a JSON string complying to the JSON-RPC 2.0 protocol, and the
size part gives the size of the JSON string in bytes.

API Objects
-----------

### `RocqSource`

- Description: Rocq source file information.
- Field `file`: a string.
- Field `dirpath`: either `null` or a string.

### `RocqLoc`

- Description: Rocq source code location.
- Field `ep`: end position (as an integer).
- Field `bp`: start position (as an integer).
- Field `bol_pos_last`: position of the beginning of end line (as an integer).
- Field `line_nb_last`: end line number (as an integer).
- Field `bol_pos`: position of the beginning of start line (as an integer).
- Field `line_nb`: start line number (as an integer).
- Field `fname`: source file identification if not run as a toplevel (as either `null` or an instance of the `RocqSource` object).

### `Quickfix`

- Description: Quick fix hint.
- Field `text`: a string.
- Field `loc`: an instance of the `RocqLoc` object.

### `FeedbackMessage`

- Description: Rocq feedback message.
- Field `text`: a string.
- Field `quickfix`: a list where each element is an instance of the `Quickfix` object.
- Field `loc`: either `null` or an instance of the `RocqLoc` object.
- Field `level`: any of `"debug"`, `"info"`, `"notice"`, `"warning"`, `"error"`.

### `GlobrefsDiff`

- Description: environment modification performed by a Rocq command.
- Field `removed_inductives`: a list where each element is a string.
- Field `added_inductives`: a list where each element is a string.
- Field `removed_constants`: a list where each element is a string.
- Field `added_constants`: a list where each element is a string.

### `ProofState`

- Description: Summary of a Rocq proof state, including the text of focused goals.
- Field `focused_goals`: a list where each element is a string.
- Field `unfocused_goals`: a list where each element is an integer.
- Field `shelved_goals`: an integer.
- Field `given_up_goals`: an integer.

### `CommandData`

- Description: data gathered while running a Rocq command.
- Field `proof_state`: either `null` or an instance of the `ProofState` object.
- Field `feedback_messages`: a list where each element is an instance of the `FeedbackMessage` object.
- Field `globrefs_diff`: an instance of the `GlobrefsDiff` object.

### `CommandError`

- Description: data returned on Rocq command errors.
- Field `feedback_messages`: a list where each element is an instance of the `FeedbackMessage` object.
- Field `error_loc`: optional source code location for the error (as either `null` or an instance of the `RocqLoc` object).

### `PrefixItem`

- Description: document prefix item, appearing before the cursor.
- Field `text`: a string.
- Field `offset`: an integer.
- Field `kind`: any of `"blanks"`, `"command"`, `"ghost"`.

### `SuffixItem`

- Description: document suffix item, appearing after the cursor.
- Field `text`: a string.
- Field `kind`: any of `"blanks"`, `"command"`, `"ghost"`.

### `CompileResult`

- Description: result of the `compile` method.
- Field `error`: non-null if success is false (as either `null` or a string).
- Field `stderr`: a string.
- Field `stdout`: a string.
- Field `success`: a boolean.

API Methods
------------

### `advance_to`

- Description: advance the cursor before the indicated unprocessed item.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - index: integer index before which to move the cursor (one-past-the-end index allowed) (as an integer).
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `CommandError` object).
- Failure mode: recoverable failure.

### `clear_suffix`

- Description: remove unprocessed commands from the document.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - count: the number of unprocessed commands to remove, or `null` to remove them all (as either `null` or an integer).
- Response payload: a `null` value.
- Failure mode: never fails.

### `clone`

- Description: clones the given cursor.
- Arguments (in order, or named):
  - cursor: the cursor to clone (as an integer).
- Response payload: the name of the new cursor (as an integer).
- Failure mode: never fails.

### `commit`

- Description: write the current document contents to the file.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - file: optional target file (as either `null` or a string).
  - include_suffix: indicate whether he suffix should be included (as a boolean).
- Response payload: a `null` value.
- Failure mode: never fails.

### `compile`

- Description: compile the current contents of the file with `rocq compile`.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: an instance of the `CompileResult` object.
- Failure mode: never fails.

### `copy_contents`

- Description: copies the contents of src into dst.
- Arguments (in order, or named):
  - src: the source cursor (as an integer).
  - dst: the target cursor (as an integer).
- Response payload: a `null` value.
- Failure mode: never fails.

### `cursor_index`

- Description: gives the index at the cursor.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: an integer.
- Failure mode: never fails.

### `dispose`

- Description: destroys the cursor.
- Arguments (in order, or named):
  - cursor: an integer.
- Response payload: a `null` value.
- Failure mode: never fails.

### `doc_prefix`

- Description: gives the list of all processed commands, appearing before the cursor.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a list where each element is an instance of the `PrefixItem` object.
- Failure mode: never fails.

### `doc_suffix`

- Description: gives the list of all unprocessed commands, appearing after the cursor.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a list where each element is an instance of the `SuffixItem` object.
- Failure mode: never fails.

### `dump`

- Description: dump the document contents (debug).
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a JSON value.
- Failure mode: never fails.

### `go_to`

- Description: move the cursor right before the indicated item (whether it is already processed or not).
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - index: integer index before which to move the cursor (one-past-the-end index allowed) (as an integer).
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `CommandError` object).
- Failure mode: recoverable failure.

### `has_suffix`

- Description: indicates whether the document has a suffix (unprocessed items).
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a boolean.
- Failure mode: never fails.

### `insert_blanks`

- Description: insert and process blanks at the cursor.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the blanks to insert (as a string).
- Response payload: a `null` value.
- Failure mode: never fails.

### `insert_command`

- Description: insert and process a command at the cursor.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the command to insert (as a string).
- Response payload: an instance of the `CommandData` object.
- Error payload: optional source code location for the error (as an instance of the `CommandError` object).
- Failure mode: recoverable failure.

### `load_file`

- Description: adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors).
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `RocqLoc` object).
- Failure mode: recoverable failure.

### `materialize`

- Description: materializes the cursor, giving it its own dedicated top-level.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: a `null` value.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `query`

- Description: runs the given query at the cursor, not updating the state.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the query (as a string).
- Response payload: an instance of the `CommandData` object.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `query_json`

- Description: runs the given query at the cursor, not updating the state.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the query (as a string).
  - index: feedback item index for the result (as an integer).
- Response payload: arbitrary JSON data, as returned by the query as JSON text, taken from the "info" / "notice" feedback with the given index (as a JSON value).
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `query_json_all`

- Description: runs the given query at the cursor, not updating the state.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the query (as a string).
  - indices: feedback indices to collect (as either `null` or a list where each element is an integer).
- Response payload: a list where each element is a JSON value.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `query_text`

- Description: runs the given query at the cursor, not updating the state.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the query (as a string).
  - index: feedback item index for the result (as an integer).
- Response payload: query's result, as taken from the "info"  "notice" feedback at the given index (as a string).
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `query_text_all`

- Description: runs the given query at the cursor, not updating the state.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the query (as a string).
  - indices: feedback indices to collect (as either `null` or a list where each element is an integer).
- Response payload: a list where each element is a string.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `revert_before`

- Description: revert the cursor to an earlier point in the document.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - erase: boolean indicating whether reverted items should be erased (as a boolean).
  - index: index of the item before which the cursor should be revered (one-past-the-end index allowed) (as an integer).
- Response payload: a `null` value.
- Failure mode: never fails.

### `run_command`

- Description: process a command at the cursor without inserting it in the document.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
  - text: text of the command to insert (as a string).
- Response payload: an instance of the `CommandData` object.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `run_step`

- Description: advance the cursor by stepping over an unprocessed item.
- Arguments (in order, or named):
  - cursor: the cursor to perform the operation on (as an integer).
- Response payload: data for the command that was run, if any (as either `null` or an instance of the `CommandData` object).
- Error payload: error data for the command that was run, if any (as either `null` or an instance of the `CommandError` object).
- Failure mode: recoverable failure.
