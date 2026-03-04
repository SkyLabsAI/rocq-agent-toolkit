from typing import override

from pydantic import BaseModel


class Err[T_err](BaseModel):
    message: str
    data: T_err


class Resp[T_resp](BaseModel):
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
