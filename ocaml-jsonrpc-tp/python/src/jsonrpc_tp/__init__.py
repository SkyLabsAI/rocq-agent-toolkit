"""Supporting Python API for the JSON-RCP-TP OCaml library.

This package provides a Python interface to interact with a JSON-RPC server
constructed with the OCaml jsonrpc-tp library. Interaction happens on the
standard input and output channels.
"""

from .jsonrpc_tp import JsonRPCTP, SyncProtocol
from .jsonrpc_tp_async import AsyncJsonRPCTP, AsyncProtocol
from .jsonrpc_tp_types import Err, Error, Resp

__all__ = [
    "AsyncJsonRPCTP",
    "AsyncProtocol",
    "Err",
    "Error",
    "JsonRPCTP",
    "Resp",
    "SyncProtocol",
]
