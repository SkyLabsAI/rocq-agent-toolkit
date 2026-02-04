from typing import Any, TypeVar, override
from warnings import deprecated

# Note: this file uses custom implementations of Reply/Err/Resp because dataclass
# doesn't play nicely with covariant data, cf. github.com/python/mypy/issues/17623
#
# TODO: use a simpler dataclass based solution that sets `__replace__ = None` when we
# fully move to pyright, cf. https://github.com/microsoft/pyright/discussions/11012;
# when we move to pydantic instead of dataclass we may still need to use an explicit
# covariant `TypeVar` here.
T_co = TypeVar("T_co", covariant=True)


class Reply[T_co]:
    """Base type of JsonRPC replies."""

    def __init__(self, data: T_co) -> None:
        self._data = data

    def __bool__(self) -> bool:
        raise NotImplementedError(
            f"implement in derivers of {self.__class__.__qualname__}"
        )

    def __eq__(self, other: Any) -> Any:
        if not issubclass(type(other), Reply):
            return NotImplemented
        return (
            type(self) is type(other)
            and type(self._data) is type(other._data)
            and self._data == other._data
        )

    @override
    def __repr__(self) -> str:
        arg_reprs = ", ".join(
            [
                f"data={repr(self.data)}",
            ]
        )
        return f"{self.__class__.__qualname__}({arg_reprs})"

    @property
    def data(self) -> T_co:
        return self._data


class Err[T_co](Reply[T_co]):
    """JSON-RPC error response, with a message and optional payload."""

    def __init__(self, message: str, data: T_co) -> None:
        super().__init__(data=data)
        self._message = message

    @override
    def __repr__(self) -> str:
        arg_reprs = ", ".join(
            [
                f"message={repr(self.message)}",
                f"data={repr(self.data)}",
            ]
        )
        return f"{self.__class__.__qualname__}({arg_reprs})"

    @override
    def __bool__(self) -> bool:
        return False

    @override
    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        return super_eq and self.message == other.message

    @property
    def message(self) -> str:
        return self._message

    # Note: we inherit data property from Reply


class Resp[T_co](Reply[T_co]):
    """Json-RPC response, with a payload."""

    def __init__(self, result: T_co) -> None:
        super().__init__(data=result)

    @override
    def __repr__(self) -> str:
        arg_reprs = ", ".join(
            [
                f"result={repr(self.result)}",
            ]
        )
        return f"{self.__class__.__qualname__}({arg_reprs})"

    @override
    def __bool__(self) -> bool:
        return True

    # Note: while we inherit the data property from Reply, we
    # prefer to use the name result.
    @override
    @property
    @deprecated("Prefer Resp.result")
    def data(self) -> T_co:
        return super().data

    @property
    def result(self) -> T_co:
        return super().data


class Error(Exception):
    """Exception raised in case of protocol error."""
