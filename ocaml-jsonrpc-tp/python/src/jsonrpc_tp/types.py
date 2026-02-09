from typing import Any, TypeVar

# Note: this file uses custom implementations of Reply/Err/Resp because dataclass
# doesn't play nicely with covariant data, cf. github.com/python/mypy/issues/17623
#
# TODO: use a simpler dataclass based solution that sets `__replace__ = None` when we
# fully move to pyright, cf. https://github.com/microsoft/pyright/discussions/11012;
# when we move to pydantic instead of dataclass we may still need to use an explicit
# covariant `TypeVar` here.
T_co = TypeVar("T_co", covariant=True)


class Err[T_co]:
    """JSON-RPC error response, with a message and optional payload."""

    def __init__(self, message: str, data: T_co) -> None:
        self._message = message
        self._data = data

    @property
    def message(self) -> str:
        return self._message

    @property
    def data(self) -> T_co:
        return self._data

    def __bool__(self) -> bool:
        return False

    def __eq__(self, other: Any) -> Any:
        if not issubclass(type(other), Err):
            return NotImplemented
        return (
            type(self) is type(other)
            and type(self._data) is type(other._data)
            and self._message == other._message
            and self._data == other._data
        )

    def __repr__(self) -> str:
        arg_reprs = ", ".join(
            [
                f"message={repr(self.message)}",
                f"data={repr(self.data)}",
            ]
        )
        return f"{self.__class__.__qualname__}({arg_reprs})"


class Resp[T_co]:
    """Json-RPC response, with a payload."""

    def __init__(self, result: T_co) -> None:
        self._result = result

    @property
    def result(self) -> T_co:
        return self._result

    def __bool__(self) -> bool:
        return True

    def __eq__(self, other: Any) -> Any:
        if not issubclass(type(other), Resp):
            return NotImplemented
        return (
            type(self) is type(other)
            and type(self._result) is type(other._result)
            and self._result == other._result
        )

    def __repr__(self) -> str:
        arg_reprs = ", ".join(
            [
                f"result={repr(self.result)}",
            ]
        )
        return f"{self.__class__.__qualname__}({arg_reprs})"


class Error(Exception):
    """Exception raised in case of protocol error."""
