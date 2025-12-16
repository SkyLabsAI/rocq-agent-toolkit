"""Composable & extensible provenance tracking for Python objects & data.

The `provenance_toolkit` levarages the W3C PROV data model (cf.
<https://www.w3.org/TR/prov-overview/>).

The `provenance_toolkit` makes it simple to compose:
- Python code-provenance (this package):
  + fine-grained & stable: track only what's relevant; minimize churn
  + lightweight hooks: decorators + metaclass injections for derivers
  + extension points: overrideable interfaces w/reasonable defaults
- data-provenance:
  + lightweight hooks (this package): decorators + metaclass injections for derivers
  + extension points: your favorite data-provenance package

Provenance is tracked at both the class and instance levels, with the goal
of disambiguating code changes over time. Tracking is done for each class
in an Provenance.Base inheritance hierarchy.

At a high level provenance can be thought of like a hash of the key parts
of a given class/instance. The provenance protocol is designed to provide
reasonable defaults in most cases so that derivers have to add minimal annotations
in order to get reasonable behavior; derivers can choose to override these
defaults.

The core class is Provenance, a namespace class consisting of:
- Provenance.Meta: metaclass for managing provenance of classes/instances
- Provenance.Base: base class for constructing Provenance.Metadata, with reasonable
    defaults
- Provenance.Metadata: class-/instance-local provenance metadata (W3C PROV data model)
- decorators for hooking into the provenance autogeneration mechanism:
  + Provenance.register: mark a method s.t. it /and/ all overrides
    in derivers are automatically tracked as part of the agent provenance
  + Provenance.compute: `Provenance.compute_as(k=<fn name>)`
  + Provenance.compute_as(k): register + use the zero-argument
    method to dynamically compute extra provenance information, tracked as `k`
- factory methods for producing whole hierarchy provenance information:
  + Provenance.provenance: instance-level
  + Provenance.cls_provenance: class-level

Note: whole hierarchy provenance information is a map from classes
in the hierarchy to (lists of) class-/instance-local provenances.

See Provenance.Base for more details.
"""

import hashlib
import json
from typing import Any, TypeAlias, final, overload

from .base import ProvenanceBase
from .meta import ProvenanceMeta
from .method_types import MethodTypes

__all__: list[str] = ["Provenance"]


class Provenance:
    """Namespace collecting classes+utilities for tracking agent provenance."""

    Base: TypeAlias = ProvenanceBase  # noqa: UP040
    Meta: TypeAlias = ProvenanceMeta  # noqa: UP040
    Metadata: TypeAlias = ProvenanceBase.Metadata  # noqa: UP040

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def register[**P, T](
        fn: MethodTypes.STATICMETHOD[P, T],
    ) -> MethodTypes.STATICMETHOD[P, T]:
        """Decorator: register staticmethod fn so it is tracked as part of provenance."""

    @staticmethod
    @overload
    def register[O, **P, T](
        fn: MethodTypes.CLASSMETHOD[O, P, T],
    ) -> MethodTypes.CLASSMETHOD[O, P, T]:
        """Decorator: register classmethod fn so it is tracked as part of provenance."""

    @staticmethod
    @overload
    def register[O, **P, T](
        fn: MethodTypes.BOUNDMETHOD[O, P, T],
    ) -> MethodTypes.BOUNDMETHOD[O, P, T]:
        """Decorator: register bound method fn so it is tracked as part of provenance."""

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def compute[T](
        fn: MethodTypes.STATICMETHOD[[], T],
    ) -> MethodTypes.STATICMETHOD[[], T]:
        """Decorator: register + use staticmethod fn to compute extra provenance data."""

    @staticmethod
    @overload
    def compute[O, T](
        fn: MethodTypes.CLASSMETHOD[O, [], T],
    ) -> MethodTypes.CLASSMETHOD[O, [], T]:
        """Decorator: register + use classmethod fn to compute extra provenance data."""

    @staticmethod
    @overload
    def compute[O, T](
        fn: MethodTypes.BOUNDMETHOD[O, [], T],
    ) -> MethodTypes.BOUNDMETHOD[O, [], T]:
        """Decorator: register + use bound method fn to compute extra provenance data."""

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters, and thinks that overload is the defn
    @final  # type: ignore[no-redef]
    @staticmethod
    def register[O, **P, T](
        fn: MethodTypes.METHOD[O, P, T],
    ) -> MethodTypes.METHOD[O, P, T]:
        """Decorator: register fn so it is tracked as part of provenance."""
        return ProvenanceMeta.track_method(fn)

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters, and thinks that overload is the defn
    @final  # type: ignore[no-redef]
    @staticmethod
    def compute[O, T](
        fn: MethodTypes.METHOD[O, [], T],
    ) -> MethodTypes.METHOD[O, [], T]:
        """Decorator: register + use fn to compute extra provenance data."""
        # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
        # same number of type parameters, and thinks that overload is the defn
        return ProvenanceMeta.track_method_mk_extra_provenance(fn)

    @staticmethod
    def metadata_of_cls(
        target_cls: type[ProvenanceBase],
        _include_sourcecode: bool = True,
    ) -> dict[type[ProvenanceBase], list[ProvenanceBase.Metadata]]:
        """Accumulate class-level provenance metadata for all members of hierarchy."""
        if not issubclass(target_cls, ProvenanceBase):
            raise TypeError(f"{target_cls} not a subclass of ProvenanceBase")
        metadata: dict[type[ProvenanceBase], list[ProvenanceBase.Metadata]] = {}
        for parent_cls in Provenance.filtered_mro(target_cls):
            if issubclass(parent_cls, ProvenanceBase):
                if parent_cls not in metadata:
                    metadata[parent_cls] = []
                metadata[parent_cls].append(
                    parent_cls.cls_provenance_metadata_of(
                        _include_sourcecode=_include_sourcecode,
                    )
                )
        return metadata

    @staticmethod
    def checksum_of_cls(
        target_cls: type[ProvenanceBase],
        _include_sourcecode: bool = True,
    ) -> str:
        if not issubclass(target_cls, ProvenanceBase):
            raise TypeError(f"{target_cls} not a subclass of ProvenanceBase")
        checksums = {
            cls.__qualname__: [metadata.checksum() for metadata in metadatas]
            for cls, metadatas in Provenance.metadata_of_cls(
                target_cls,
                _include_sourcecode=_include_sourcecode,
            ).items()
        }
        checksums_json = json.dumps(checksums, sort_keys=True, ensure_ascii=False)
        checksums_bytes = checksums_json.encode("utf-8")
        return hashlib.md5(checksums_bytes).hexdigest()

    @staticmethod
    def of_cls(
        target_cls: type[ProvenanceBase],
        _include_sourcecode: bool = True,
    ) -> dict[str, list[dict[str, Any]]]:
        """Accumulate class-level provenance for all members of hierarchy."""
        if not issubclass(target_cls, ProvenanceBase):
            raise TypeError(f"{target_cls} not a subclass of ProvenanceBase")
        return {
            cls.__qualname__: [metadata.provenance() for metadata in metadatas]
            for cls, metadatas in Provenance.metadata_of_cls(
                target_cls,
                _include_sourcecode=_include_sourcecode,
            ).items()
        }

    @staticmethod
    def metadata_of(
        target_this: ProvenanceBase,
        _include_sourcecode: bool = True,
    ) -> dict[type[ProvenanceBase], list[ProvenanceBase.Metadata]]:
        """Accumulate instance-level provenance metadata for all members of hierarchy."""
        if not issubclass(type(target_this), ProvenanceBase):
            raise TypeError(f"{type(target_this)} not a subclass of ProvenanceBase")
        metadata: dict[type[ProvenanceBase], list[ProvenanceBase.Metadata]] = {}
        for parent_cls in Provenance.filtered_mro(target_this.__class__):
            if issubclass(parent_cls, ProvenanceBase):
                if parent_cls not in metadata:
                    metadata[parent_cls] = []
                metadata[parent_cls].append(
                    parent_cls.provenance_metadata_of(
                        target_this,
                        _include_sourcecode=_include_sourcecode,
                    )
                )
        return metadata

    @staticmethod
    def checksum_of(
        target_this: ProvenanceBase,
        _include_sourcecode: bool = True,
    ) -> str:
        if not issubclass(type(target_this), ProvenanceBase):
            raise TypeError(f"{type(target_this)} not a subclass of ProvenanceBase")
        checksums = {
            cls.__qualname__: [metadata.checksum() for metadata in metadatas]
            for cls, metadatas in Provenance.metadata_of(
                target_this,
                _include_sourcecode=_include_sourcecode,
            ).items()
        }
        checksums_json = json.dumps(checksums, sort_keys=True, ensure_ascii=False)
        checksums_bytes = checksums_json.encode("utf-8")
        return hashlib.md5(checksums_bytes).hexdigest()

    @staticmethod
    def of(
        target_this: ProvenanceBase,
        _include_sourcecode: bool = True,
    ) -> dict[str, list[dict[str, Any]]]:
        """Accumulate instance-level provenance for all members of hierarchy."""
        if not issubclass(type(target_this), ProvenanceBase):
            raise TypeError(f"{type(target_this)} not a subclass of ProvenanceBase")
        return {
            cls.__qualname__: [metadata.provenance() for metadata in metadatas]
            for cls, metadatas in Provenance.metadata_of(
                target_this,
                _include_sourcecode=_include_sourcecode,
            ).items()
        }

    @staticmethod
    def filtered_mro[O: ProvenanceBase](
        target_cls: type[O],
    ) -> list[type[ProvenanceBase]]:
        """MRO for cls, keeping only classes derived from ProvenanceBase."""
        bases = []
        for base_cls in target_cls.mro():
            if issubclass(base_cls, ProvenanceBase):
                bases.append(base_cls)
        return bases
