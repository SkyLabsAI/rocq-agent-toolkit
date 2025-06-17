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

Transfer Protocol
-----------------

Packets sent to / received from the document manager have the following shape.
```
Content-Length: <size>\r\n\r\n<data>
```
The data part is a JSON string complying to the JSON-RPC 2.0 protocol, and the
size part gives the size of the JSON string in bytes.

Supported Requests
------------------

### `load_file`

- Arguments: none.
- Description: add the (unprocessed) file contents to the document.
- Failure mode: never fails.
- Response payload: `null`.

### `insert_blanks`

- Arguments: `text` (string).
- Description: insert and process blanks at the cursor.
- Failure mode: never fails.
- Response payload: `null`.

### `insert_command`

- Arguments: `text` (string)
- Description: insert and process a command at the cursor.
- Failure mode: recoverable failure.
- Failure payload: object with `loc` field (error location, `null` if none).
- Response payload: object with `open_subgoals` (null or string),
  `new_constants` (string list), `new_inductives` (string list).

### `run_command`

- Arguments: `text` (string)
- Description: process a command, without inserting it in the document.
- Failure mode: recoverable failure.
- Failure payload: object with `loc` field (error location, `null` if none).
- Response payload: object with `open_subgoals` (null or string),
  `new_constants` (string list), `new_inductives` (string list).

### `cursor_index`

- Arguments: none.
- Description: gives the index at the cursor.
- Failure mode: never fails.
- Response payload: integer.

### `revert_before`

- Arguments: `erase` (boolean), `index` (integer).
- Description: revert the cursor before the indicated processed item, erasing
  the reverted commands as instructed.
- Failure mode: never fails, panic on invalid `index`.
- Response payload: `null`.

### `advance_to`

- Arguments: `index` (integer).
- Description: advance the cursor before the indicated unprocessed item
  (one-past-the-end index allowed).
- Failure mode: recoverable failure, panic on invalid `index`.
- Failure payload: object with `loc` field (error location, `null` if none).
- Response payload: `null`.

### `clear_suffix`

- Arguments: none.
- Description: remove all unprocessed commands from the document.
- Failure mode: never fails.
- Response payload: `null`.

### `run_step`

- Arguments: none.
- Description: advance the cursor by stepping over an unprocessed item.
- Failure mode: recoverable failure.
- Failure payload: object with `loc` field (error location, `null` if none).
- Response payload: `null` if a blank step was run, same as `insert_command`
  otherwise.

### `doc_prefix`

- Arguments: none.
- Description: give the list of all processed commands (before the cursor).
- Failure mode: never fails.
- Response payload: list of objects with `kind` (string, using `"blanks"` for
  blanks), `offset` (integer), and `text` (string).

### `doc_suffix`

- Arguments: none.
- Description: give the list of all unprocessed commands (after the cursor).
- Failure mode: never fails.
- Response payload: list of objects with `kind` (string, using `"blanks"` for
  blanks), and `text` (string).

### `has_suffix`

- Arguments: none.
- Description: indicates whether there is a document suffix.
- Failure mode: never fails.
- Response payload: boolean.

### `commit`

- Arguments: `include_suffix` (boolean).
- Description: write the current document contents to the file, including the
  unprocessed suffix as instructed.
- Failure mode: never fails.
- Response payload: `null`.

### `compile`

- Arguments: none.
- Description: compile the current contents of the file with `rocq compile`.
- Failure mode: never fails.
- Response payload: object with `success` (boolean), `stdout` (string),
  `stderr` (string), `error` (string, only if success is `false`).

### `get_feedback`

- Arguments: none.
- Description: gets Rocq's feedback for the last run command.
- Failure mode: never fails.
- Response payload: list of objects with `kind` (array with single string),
  `text` (string), `loc` (location).

### `text_query`

- Arguments: `text` (string), `index` (integer).
- Description: runs the given query at the cursor, not updating the state.
- Failure mode: recoverable failure.
- Failure payload: none.
- Response payload: string with the query's result (as taken from the "notice"
  feedback with the given index).

### `json_query`

- Arguments: `text` (string), `index` (integer).
- Description: runs the given query at the cursor, not updating the state.
- Failure mode: recoverable failure.
- Failure payload: none.
- Response payload: arbitrary JSON data, as returned by the query (as JSON
  text, take from the "notice" feedback with the given index).

### `quit`

- Arguments: none.
- Description: stop the document manager (sub-process terminated).
- Failure mode: never fails.
- Response payload: `null`.
