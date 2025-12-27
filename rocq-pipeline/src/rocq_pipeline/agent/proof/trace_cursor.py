import functools
import hashlib
from collections.abc import Callable
from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager_api import RocqDocManagerAPI

logger = get_logger("RocqCursor")


def _trace_log(
    *,
    after: bool = False,
    cmd: Callable[[dict[str, Any]], str] | None = None,
    inputs_ex: Callable[[RocqCursor, dict[str, Any]], Any] | None = None,
    inputs: Callable[[dict[str, Any]], dict[str, Any]] | None = None,
    output: Callable[[Any], Any] | None = None,
    exception: Callable[[Any], Any] | None = None,
):
    def wrap(func: Callable):
        @functools.wraps(func)
        def wrapper(self, **args):
            # it is important that we get the location before we run the function
            location = self._location()
            log_args = {"state_id": location}
            if inputs_ex:
                assert inputs is None
                log_args["args"] = inputs_ex(self, args)
            elif inputs:
                log_args["args"] = inputs(args)
            else:
                log_args["args"] = args
            if cmd:
                log_args["action"] = cmd(args)
            try:
                result = func(self, **args)
                if output:
                    log_args["result"] = output(result)
                else:
                    log_args["result"] = result
                if after:
                    log_args["next_state_id"] = self._location()
                logger.info(f"RocqCursor.{func.__name__}", **log_args)
            except Exception as err:
                if exception:
                    log_args["exception"] = exception(err)
                else:
                    log_args["exception"] = err
                logger.info(f"RocqCursor.{func.__name__}", **log_args)
                raise

        return wrapper

    return wrap


class TracingCursor(RocqCursor):
    """
    An implementation of the RocqCursor API that traces all document interactions recording
    a state_id.
    """

    def __init__(self, rdm: RocqDocManagerAPI, cursor: int) -> None:
        super().__init__(rdm, cursor)

    def _location(self) -> str:
        """Construct a functional location by computing the hash of the effectful commands."""
        raw = "\n".join(
            [elem.text for elem in self.doc_prefix() if elem.kind == "command"]
        )
        return hashlib.md5(raw.encode("utf-8")).hexdigest()

    @override
    def clone(self, materialize: bool = False):
        # We don't trace this because we don't care about the actual cursor, but we do care that the cloned cursor is also traced
        result = super().clone(materialize=materialize)
        assert result._the_rdm is not None
        return TracingCursor(result._the_rdm, result._cursor)

    @override
    @_trace_log(after=True, inputs=lambda args: args["text"])
    def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return super().insert_command(text, blanks, safe)

    @override
    @_trace_log(after=True, inputs=lambda args: args["text"])
    def run_command(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().run_command(text)

    @staticmethod
    def _next_command(me: RocqCursor, args: dict[str, Any]) -> str | None:
        suffix = [item.text for item in me.doc_suffix() if item.kind == "command"]
        return suffix[0]

    @override
    @_trace_log(after=True, inputs_ex=_next_command)
    def run_step(
        self,
    ) -> RocqCursor.CommandData | None | RocqCursor.Err[RocqCursor.CommandError | None]:
        return super().run_step()

    @override
    @_trace_log(after=False, inputs=lambda args: args["text"])
    def query(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().query(text)

    @override
    @_trace_log(after=False, inputs=lambda args: args["text"])
    def query_json(
        self, text: str, index: int
    ) -> Any | RocqCursor.Err[RocqCursor.CommandError]:
        return super().query_json(text, index)

    @override
    @_trace_log(after=False, inputs=lambda args: args["text"])
    def query_json_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[Any] | RocqCursor.Err[None]:
        return super().query_json_all(text, indices)

    @override
    @_trace_log(after=False, inputs=lambda args: args["text"])
    def query_text(self, text: str, index: int) -> str | RocqCursor.Err[None]:
        return super().query_text(text, index)

    @override
    @_trace_log(after=False, inputs=lambda args: args["text"])
    def query_text_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[str] | RocqCursor.Err[None]:
        return super().query_text_all(text, indices)
