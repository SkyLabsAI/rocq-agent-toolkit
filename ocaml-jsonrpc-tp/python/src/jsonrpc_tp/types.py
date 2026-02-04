from dataclasses import dataclass

# Note: dataclass doesn't play nicely with covariant data, cf.
# https://discuss.python.org/t/make-replace-stop-interfering-with-variance-inference/96092/41


# We use a workaround from the thread above that simply sets `__replace__ = None`
@dataclass
class Err[T]:
    """JSON-RPC error response, with a message and payload."""

    __replace__ = None
    message: str
    data: T


@dataclass
class Resp[R]:
    """JSON-RPC response, with a payload."""

    __replace__ = None
    result: R


class Error(Exception):
    """Exception raised in case of protocol error."""
