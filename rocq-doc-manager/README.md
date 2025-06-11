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

The following table lists the available requests.

| Method Name      | Argument Types          | Description                                                   |
| ---------------- | ----------------------- | ------------------------------------------------------------- |
| `load_file`      |                         | Add the (unprocessed) file contents to the document.          |
| `insert_blanks`  | `text` (string)         | Insert and process blanks at the cursor.                      |
| `insert_command` | `text` (string)         | Insert and process a command at the cursor.                   |
| `run_command`    | `text` (string)         | Process a command, without inserting it in the document.      |
| `revert_before`  | `index` (int)           | Revert the cursor before the indicated processed item.        |
| `clear_suffix`   |                         | Remove all unprocessed commands from the document.            |
| `run_step`       |                         | Advance the cursor by stepping over an unprocessed command.   |
| `doc_prefix`     |                         | Give the list of all processed commands (before the cursor).  |
| `doc_suffix`     |                         | Give the list of all unprocessed commands (after the cursor). |
| `has_suffix`     |                         | Indicates whether there is a document suffix.                 |
| `commit`         | `include_suffix` (bool) | Write the current document contents to the file.              |
| `compile`        |                         | Compile the current contents of the file with `rocq compile`. |
| `get_feedback`   |                         | Gets Rocq's feedback for the last run command.                |
| `text_query`     | `text` (string)         | Runs the given query at the cursor, not updating the state.   |
| `json_query`     | `text` (string)         | Runs the given query at the cursor, not updating the state.   |
| `quit`           |                         | Stop the document manager.                                    |

Requests That Can Fail
----------------------

The following table indicates what commands can fail, and whether they have an
extra failure payload.

| Method Name      | Can Fail? | Error Payload (Excluding Message)                         |
| ---------------- | --------- | --------------------------------------------------------- |
| `load_file`      | Yes       |                                                           |
| `insert_blanks`  | No        |                                                           |
| `insert_command` | Yes       | Object with `loc` field (error location, `null` if none). |
| `run_command`    | Yes       |                                                           |
| `revert_before`  | No        |                                                           |
| `clear_suffix`   | No        |                                                           |
| `run_step`       | Yes       | Object with `loc` field (error location, `null` if none). |
| `doc_prefix`     | No        |                                                           |
| `doc_suffix`     | No        |                                                           |
| `has_suffix`     | No        |                                                           |
| `commit`         | No        |                                                           |
| `compile`        | No        |                                                           |
| `get_feedback`   | No        |                                                           |
| `text_query`     | Yes       |                                                           |
| `json_query`     | Yes       |                                                           |
| `quit`           | No        |                                                           |

Response Payload
----------------

The following table indicates what the payload of the response is for requests
that don't have a trivial (i.e., `null`) response payload.

| Method Name      | Response Payload                                                                                                  |
| ---------------- | ----------------------------------------------------------------------------------------------------------------- |
| `load_file`      |                                                                                                                   |
| `insert_blanks`  |                                                                                                                   |
| `insert_command` | Object with `open_subgoals` (null or string), `new_constants` (string list), `new_inductives` (string list).      |
| `run_command`    | Object with `open_subgoals` (null or string), `new_constants` (string list), `new_inductives` (string list).      |
| `revert_before`  |                                                                                                                   |
| `clear_suffix`   |                                                                                                                   |
| `run_step`       | Just `null` if a blank step was run, same as `insert_command` otherwise.                                          |
| `doc_prefix`     | List of objects with `kind` (string, `"blanks"` for blanks), `offset` (int), and `text` (string).                 |
| `doc_suffix`     | List of objects with `kind` (string, `"blanks"` for blanks), and `text` (string).                                 |
| `has_suffix`     | Boolean.                                                                                                          |
| `commit`         |                                                                                                                   |
| `compile`        | Object with `success` (bool), `stdout` (string), `stderr` (string), `error` (string, only if success is `false`). |
| `get_feedback`   | List of objects with `kind` (array with single string), `text` (string), `loc` (location).                        |
| `text_query`     | String with the query's result (as taken from a "notice" feedback item.                                           |
| `json_query`     | Arbitrary JSON data, as returned by the query (as JSON text, in a notice" feed back item).                        |
| `quit`           |                                                                                                                   |
