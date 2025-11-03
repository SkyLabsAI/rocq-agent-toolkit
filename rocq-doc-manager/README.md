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

### `rocq_source`

- Description: Rocq source file information.
- Field `file`: a string.
- Field `dirpath`: either `null` or a string.

### `rocq_loc`

- Description: Rocq source code location.
- Field `ep`: end position (as an integer).
- Field `bp`: start position (as an integer).
- Field `bol_pos_last`: position of the beginning of end line (as an integer).
- Field `line_nb_last`: end line number (as an integer).
- Field `bol_pos`: position of the beginning of start line (as an integer).
- Field `line_nb`: start line number (as an integer).
- Field `fname`: source file identification if not run as a toplevel (as either `null` or an instance of the `rocq_source` object).

### `command_data`

- Description: data gathered while running a Rocq command.
- Field `removed_inductives`: inductives removed by the command (as a list where each element is a string).
- Field `new_inductives`: inductives introduced by the command (as a list where each element is a string).
- Field `removed_constants`: constants removed by the command (as a list where each element is a string).
- Field `new_constants`: constants introduced by the command (as a list where each element is a string).
- Field `open_subgoals`: open sub-goals, if in a proof (as either `null` or a string).

### `revert_config`

- Description: input configuration for the `revert_before` method.
- Field `index`: index of the item before which the cursor should be revered (one-past-the-end index allowed) (as an integer).
- Field `erase`: boolean indicating whether reverted items should be erased (as a boolean).

### `prefix_item`

- Description: document prefix item, appearing before the cursor.
- Field `text`: a string.
- Field `offset`: an integer.
- Field `kind`: a string.

### `suffix_item`

- Description: document suffix item, appearing after the cursor.
- Field `text`: a string.
- Field `kind`: a string.

### `compile_result`

- Description: result of the `compile` method.
- Field `error`: non-null if success is false (as either `null` or a string).
- Field `success`: a boolean.
- Field `stderr`: a string.
- Field `stdout`: a string.

### `query_config`

- Description: input config for queries.
- Field `index`: an integer.
- Field `text`: a string.

### `query_all_config`

- Description: input config for multi-result queries.
- Field `indices`: either `null` or a list where each element is an integer.
- Field `text`: a string.

API Methods
------------

### `advance_to`

- Description: advance the cursor before the indicated unprocessed item.
- Argument: integer index before which to advance the cursor (one-past-the-end index allowed) (as an integer).
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `rocq_loc` object).
- Failure mode: recoverable failure.

### `clear_suffix`

- Description: remove all unprocessed commands from the document.
- Argument: a `null` value.
- Response payload: a `null` value.
- Failure mode: never fails.

### `commit`

- Description: write the current document contents to the file.
- Argument: indicate whether he suffix should be included (as a boolean).
- Response payload: a `null` value.
- Failure mode: never fails.

### `compile`

- Description: compile the current contents of the file with `rocq compile`.
- Argument: a `null` value.
- Response payload: an instance of the `compile_result` object.
- Failure mode: never fails.

### `cursor_index`

- Description: gives the index at the cursor.
- Argument: a `null` value.
- Response payload: an integer.
- Failure mode: never fails.

### `doc_prefix`

- Description: gives the list of all processed commands, appearing before the cursor.
- Argument: a `null` value.
- Response payload: a list where each element is an instance of the `prefix_item` object.
- Failure mode: never fails.

### `doc_suffix`

- Description: gives the list of all unprocessed commands, appearing after the cursor.
- Argument: a `null` value.
- Response payload: a list where each element is an instance of the `suffix_item` object.
- Failure mode: never fails.

### `get_feedback`

- Description: gets Rocq's feedback for the last run command (if any).
- Argument: a `null` value.
- Response payload: list of objects with `kind` (array with single string), `text` (string), `loc` (location) (as a list where each element is a JSON value).
- Failure mode: never fails.

### `go_to`

- Description: move the cursor right before the indicated item (whether it is already processed or not).
- Argument: integer index before which to advance the cursor (one-past-the-end index allowed) (as an integer).
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `rocq_loc` object).
- Failure mode: recoverable failure.

### `has_suffix`

- Description: indicates whether the document has a suffix (unprocessed items).
- Argument: a `null` value.
- Response payload: a boolean.
- Failure mode: never fails.

### `insert_blanks`

- Description: insert and process blanks at the cursor.
- Argument: a string.
- Response payload: a `null` value.
- Failure mode: never fails.

### `insert_command`

- Description: insert and process a command at the cursor.
- Argument: a string.
- Response payload: an instance of the `command_data` object.
- Error payload: optional source code location for the error (as either `null` or an instance of the `rocq_loc` object).
- Failure mode: recoverable failure.

### `json_query`

- Description: runs the given query at the cursor, not updating the state.
- Argument: an instance of the `query_config` object.
- Response payload: arbitrary JSON data, as returned by the query as JSON text, taken from the "info" / "notice" feedback with the given index (as a JSON value).
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `load_file`

- Description: adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors).
- Argument: a `null` value.
- Response payload: a `null` value.
- Error payload: optional source code location for the error (as either `null` or an instance of the `rocq_loc` object).
- Failure mode: recoverable failure.

### `revert_before`

- Description: revert the cursor to an earlier point in the document.
- Argument: an instance of the `revert_config` object.
- Response payload: a `null` value.
- Failure mode: never fails.

### `run_command`

- Description: process a command at the cursor without inserting it in the document.
- Argument: a string.
- Response payload: an instance of the `command_data` object.
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `run_step`

- Description: advance the cursor by stepping over an unprocessed item.
- Argument: a `null` value.
- Response payload: data for the command that was run, if any (as either `null` or an instance of the `command_data` object).
- Error payload: optional source code location for the error (as either `null` or an instance of the `rocq_loc` object).
- Failure mode: recoverable failure.

### `text_query`

- Description: runs the given query at the cursor, not updating the state.
- Argument: an instance of the `query_config` object.
- Response payload: query's result, as taken from the "info"  "notice" feedback at the given index (as a string).
- Error payload: a `null` value.
- Failure mode: recoverable failure.

### `text_query_all`

- Description: runs the given query at the cursor, not updating the state.
- Argument: an instance of the `query_all_config` object.
- Response payload: a list where each element is a string.
- Error payload: a `null` value.
- Failure mode: recoverable failure.
