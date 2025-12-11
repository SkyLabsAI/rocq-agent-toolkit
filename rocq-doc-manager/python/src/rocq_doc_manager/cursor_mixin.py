from __future__ import annotations

import logging
import re
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager
from typing import Any, Literal, Self, override
from warnings import deprecated

from rocq_doc_manager.rocq_cursor_protocol import RocqCursorProtocol

from .rocq_doc_manager_api import RocqDocManagerAPI as API

logger = logging.getLogger(__name__)


class CursorMixin(RocqCursorProtocol):
    """
    Implementors of the RocqCursor API can inherit this class to provide
    additional member functions.
    """
