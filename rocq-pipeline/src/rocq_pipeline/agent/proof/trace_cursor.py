import functools
import hashlib
from typing import override

from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager_api import RocqDocManagerAPI

logger = get_logger("RocqCursor")


def _trace_log(*, after: bool = False):
    def wrap(func):
        @functools.wraps(func)
        def wrapper(self, **args):
            # it is important that we get the location before we run the function
            location = self._location()
            try:
                result = func(self, **args)
                if after:
                    logger.info(
                        f"RocqCursor.{func.__name__}",
                        state_id=location,
                        args=args,
                        result=result,
                        next_state_id=self._location(),
                    )
                else:
                    logger.info(
                        f"RocqCursor.{func.__name__}",
                        state_id=location,
                        args=args,
                        result=result,
                    )
            except Exception as err:
                logger.info(
                    f"RocqCursor.{func.__name__}",
                    state_id=location,
                    args=args,
                    exception=err,
                )
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
        result = super().clone(materialize=materialize)
        assert result._the_rdm is not None
        return TracingCursor(result._the_rdm, result._cursor)

    @override
    @_trace_log(after=True)
    def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return super().insert_command(text, blanks, safe)

    @override
    @_trace_log(after=True)
    def run_command(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().run_command(text)

    @override
    @_trace_log(after=True)
    def run_step(
        self,
    ) -> RocqCursor.CommandData | None | RocqCursor.Err[RocqCursor.CommandError | None]:
        return super().run_step()

    @override
    @_trace_log(after=False)
    def query(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().query(text)

    @override
    @_trace_log(after=False)
    def query_json(
        self, text: str, index: int
    ) -> Any | RocqCursor.Err[RocqCursor.CommandError]:
        return super().query_json(text, index)

    @override
    @_trace_log(after=False)
    def query_json_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[Any] | RocqCursor.Err[None]:
        return super().query_json_all(text, indices)

    @override
    @_trace_log(after=False)
    def query_text(self, text: str, index: int) -> str | RocqCursor.Err[None]:
        return super().query_text(text, index)

    @override
    @_trace_log(after=False)
    def query_text_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[str] | RocqCursor.Err[None]:
        return super().query_text_all(text, indices)
