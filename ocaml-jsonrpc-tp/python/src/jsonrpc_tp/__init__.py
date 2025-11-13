"""Supporting Python API for the JSON-RCP-TP OCaml library.

This package provides a Python interface to interact with a JSON-RPC server
constructed with the OCaml jsonrpc-tp library. Interaction happens on the
standard input and output channels.
"""

from .jsonrpc_tp import Err, Error, JsonRPCTP, Resp

__all__ = [
    "Err",
    "Resp",
    "Error",
    "JsonRPCTP",
]
