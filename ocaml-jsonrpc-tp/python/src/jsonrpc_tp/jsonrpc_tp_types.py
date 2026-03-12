from typing import final, override

from pydantic import BaseModel


@final
class Err[T_err](BaseModel, frozen=True):
    message: str
    data: T_err


@final
class Resp[T_resp](BaseModel, frozen=True):
    result: T_resp


class Error(Exception):
    """Exception raised in case of protocol error."""

    def __init__(self, *args, stderr: str | None = None) -> None:
        super().__init__(*args)
        self.stderr = stderr

    @override
    def __str__(self) -> str:
        if self.stderr:
            return f"{super().__str__()}\n(stderr='{self.stderr}')"
        else:
            return super().__str__()
