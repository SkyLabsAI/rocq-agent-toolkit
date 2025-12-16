"""Core metaclass: auto-provenance generation and raw decorator extension hooks."""

from __future__ import annotations

import logging
from typing import Any

from .meta_util import ProvenanceMetaHelper

logger = logging.getLogger(__name__)


class ProvenanceMeta(ProvenanceMetaHelper):
    """Metaclass for the Provenance protocol.

    Propogate tracking information to enable automatic construction
    of provenance based on client usage of decorators exposed in
    __init__.py#Provenance.
    """

    # Note: as of Python 3.13, metaclasses should not contain custom
    # logic in `__new__` after the `super().__new__` call.
    #
    # cf. https://docs.python.org/3/whatsnew/3.13.html#ctypes
    def __new__(
        mcs,
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
        **kwargs: Any,
    ) -> ProvenanceMeta:
        # Perform transitive method tracking and mutate namespace as necessary
        mcs.transitive_method_tracking(name, bases, namespace)
        return super().__new__(mcs, name, bases, namespace)
