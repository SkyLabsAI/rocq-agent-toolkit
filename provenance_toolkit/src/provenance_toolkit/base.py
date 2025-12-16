"""Base types used for defining Provenance, cf. __init__.py."""

from __future__ import annotations

import hashlib
import inspect
import json
import logging
from collections.abc import Collection
from dataclasses import dataclass, field
from typing import Any

from .meta import ProvenanceMeta
from .meta_util import ProvenanceMetaTracking
from .method_types import MethodTypes

logger = logging.getLogger(__name__)


class ProvenanceBase(metaclass=ProvenanceMeta):
    """Core interface for capturing agent provenance.

    Note: ProvenanceMeta contains the extension points & defaults;
    this class contains utilities for computing provenance (metadata) at a
    specific point in the inheritance hierarchy.
    """

    VERSION = "0.0.1"

    @classmethod
    def cls_provenance_metadata_of(
        cls,
        _include_sourcecode: bool = True,
    ) -> ProvenanceBase.Metadata:
        """DO NOT OVERRIDE: class-level metadata; used by Provenance."""
        # NOTE: always explicitly track the `VERSION` of the Provenance protocol
        cls_extra = cls.mk_provenance_cls_extra()
        if cls is ProvenanceBase:
            cls_extra["VERSION"] = ProvenanceBase.VERSION

        return ProvenanceBase.Metadata(
            _include_sourcecode=_include_sourcecode,
            cls=cls,
            cls_code=cls.mk_provenance_cls_code(),
            cls_extra=cls_extra,
        )

    @classmethod
    def provenance_metadata_of(
        cls,
        this: ProvenanceBase,
        _include_sourcecode: bool = True,
    ) -> ProvenanceBase.Metadata:
        """DO NOT OVERRIDE: instance-level metadata; used by Provenance."""
        assert issubclass(this.__class__, cls), (
            f"{this.__class__} not subclass of {cls}"
        )

        # NOTE: always explicitly track the `VERSION` of the Provenance protocol
        cls_extra = cls.mk_provenance_cls_extra()
        if cls is ProvenanceBase:
            cls_extra["VERSION"] = ProvenanceBase.VERSION

        return ProvenanceBase.Metadata(
            _include_sourcecode=_include_sourcecode,
            cls=cls,
            cls_code=cls.mk_provenance_cls_code(),
            cls_extra=cls_extra,
            this=this,
            extra=cls.mk_provenance_extra(this),
        )

    @classmethod
    def mk_provenance_cls_code(
        cls,
    ) -> dict[str, MethodTypes.METHOD[ProvenanceBase, ..., Any]]:
        return {
            nm: cls.__dict__[nm] for nm in ProvenanceMetaTracking.lookup(cls).methods
        }

    @classmethod
    def mk_provenance_cls_extra(cls) -> dict[str, Any]:
        cls_extra: dict[str, Any] = {}
        tracking: ProvenanceMetaTracking = ProvenanceMetaTracking.lookup(cls)

        for nm, method in cls.mk_provenance_cls_code().items():
            if MethodTypes.is_staticmethod(method, cls=cls):
                if nm not in tracking.staticmethods_compute_extra:
                    continue
                cls_extra[method.__name__] = method.__func__()
            elif MethodTypes.is_classmethod(method, cls=cls):
                if nm not in tracking.classmethods_compute_extra:
                    continue
                cls_extra[method.__name__] = method.__func__(cls)
            else:
                continue

        return cls_extra

    @classmethod
    def mk_provenance_extra(cls, this: ProvenanceBase) -> dict[str, Any]:
        extra: dict[str, Any] = {}
        tracking: ProvenanceMetaTracking = ProvenanceMetaTracking.lookup(cls)

        for nm, method in cls.mk_provenance_cls_code().items():
            if MethodTypes.is_boundmethod(method, cls=cls):
                if nm not in tracking.boundmethods_compute_extra:
                    continue
                extra[method.__name__] = method(this)
            else:
                continue

        return extra

    @dataclass(frozen=True)
    class Metadata:
        """Provenance of one class in a hierarchy of ProvenanceProviders.

        Provenance information is stored in rich form and supports serialization
        to JSON, but not deserialization. The same metadata type is used used
        for both class- and instance-level provenance information, with the
        former using None values for all instance-level fields. Note: provenance
        is always compared using the serialized view.

        At the class-level, provenance for an agent consists of:
        - cls (type[O]): the class this metadata is for
        - bases (list[type[O]]): direct bases using provenance protocol
        - code (dict[str, FunctionType]): the salient class functions+methods
        - extra (dict[str, Any]): any additional KV-pairs

        At the instance-level, provenance for an agent consists of:
        - this (O): the instance
        - extra (dict[str, Any]): any additional KV-pairs

        Agents do not directly manage metadata construction. Instead, they use
        decorators to mark code which should be tracked as part of provenance
        (and potentially used to compute extra provenance information); cf.
        __init__.py#Provenance.
        """

        # Hooks
        _include_sourcecode: bool = field(kw_only=True, default=True)

        # Provenance for the class
        cls: type[ProvenanceBase] = field(kw_only=True)
        cls_bases: list[type[ProvenanceBase]] = field(
            kw_only=True,
            init=False,
        )
        cls_code: dict[str, MethodTypes.METHOD[ProvenanceBase, ..., Any]] = field(
            kw_only=True,
            default_factory=dict,
        )
        cls_extra: dict[str, Any] = field(kw_only=True, default_factory=dict)

        # Provenance for the (derived) instance
        this: ProvenanceBase | None = field(kw_only=True, default=None)
        extra: dict[str, Any] | None = field(kw_only=True, default=None)

        def provenance(self) -> dict[str, Any]:
            """Provenance from Metadata."""

            def _val_provenance(nm: str, v: Any) -> Any:
                # Note: clients can choose how they want to produce
                # the (str) provenance information for FunctionType
                if MethodTypes.is_method(v, cls=self.cls):
                    if self._include_sourcecode:
                        fn_raw: MethodTypes.RAW_METHOD[ProvenanceBase, ..., Any]
                        if MethodTypes.is_staticmethod(
                            v, cls=self.cls
                        ) or MethodTypes.is_classmethod(v, cls=self.cls):
                            fn_raw = v.__func__
                        else:
                            fn_raw = v

                        try:
                            return inspect.getsource(fn_raw)
                        except (OSError, TypeError):
                            # Gracefully degrade if source is unavailable
                            # (e.g., in binary distributions without .py files)
                            return "<unavailable>"
                    else:
                        return v.__name__

                # Use repr(v) if json.dumps fails, else return v unchanged
                try:
                    _ = json.dumps(v)
                except json.JSONDecodeError:
                    v_repr: str = repr(v)
                    logger.warning(f"json.dump failed for {nm}, using repr ({v_repr})")
                    return v_repr
                return v

            prov: dict[str, Any] = {
                "cls": self.cls.__qualname__,
                "bases": [base.__qualname__ for base in self.cls_bases],
                # Note: intentionally elide self.this
            }
            prov.update(
                {
                    field_nm: {nm: _val_provenance(nm, v) for nm, v in mapping.items()}
                    for field_nm, mapping in {
                        "cls_code": self.cls_code,
                        "cls_extra": self.cls_extra,
                        "extra": self.extra or {},
                    }.items()
                },
            )
            self.wellformed_provenance(prov, strict=True)
            return prov

        def checksum(self) -> str:
            """Compute a stable checksum/hash of the serialized provenance.

            Returns an MD5 hash (hex string) of the JSON-serialized provenance.
            This can be used as a pseudo-unique primary key for the agent identity.
            """
            prov = self.provenance()
            # Ensure deterministic serialization by sorting dict keys
            prov_json = json.dumps(prov, sort_keys=True, ensure_ascii=False)
            prov_bytes = prov_json.encode("utf-8")
            return hashlib.md5(prov_bytes).hexdigest()

        @staticmethod
        def wellformed_provenance(provenance: Any, strict: bool = False) -> bool:
            def _illformed(msg: str, exc: Exception | None = None) -> None:
                logger.warning(msg)
                new_exc = AssertionError(msg)
                if exc:
                    raise new_exc from exc
                else:
                    raise new_exc

            try:
                if not isinstance(provenance, dict):
                    _illformed(f"expected dict but got {type(provenance)}")

                schema = ProvenanceBase.Metadata.provenance_schema()
                if not provenance.keys() == schema.keys():
                    _illformed(f"{provenance.keys()} != {schema.keys()}")

                def _wellformed_provenance_value(
                    v: Any,
                    v_ty: type,
                ) -> None:
                    try:
                        if not isinstance(v, v_ty):
                            _illformed(f"expected {v_ty} but got ({type(v)}) {v}")
                    except TypeError:
                        logger.info(
                            f"ProvenanceBase.Metadata: failed to use {v_ty} to typecheck {v}"
                        )

                    try:
                        _ = json.dumps(v)
                    except json.JSONDecodeError as e:
                        _illformed(f"{v} is not serializable", exc=e)

                for k, v_ty in schema.items():
                    v = provenance[k]

                    # Note: provenance_schema uses tuple for containers;
                    # dict requires key type of str, and the schema is only
                    # one level deep
                    if isinstance(v_ty, tuple):
                        assert len(v_ty) == 2 and (
                            v_ty[0] is list or v_ty[0] is dict
                        ), "ProvenanceBase.Metadata.provenance_schema broken"
                        if not isinstance(v, v_ty[0]):
                            _illformed(f"expected {v_ty} but got ({type(v)}) {v}")

                        c: Collection[Any]
                        if v_ty[0] is list:
                            assert isinstance(v, list)
                            c = v
                        elif v_ty[0] is set:
                            assert isinstance(v, set)
                            c = v
                        elif v_ty[0] is dict:
                            assert isinstance(v, dict)
                            c = v.values()
                        else:
                            raise TypeError(
                                f"{v_ty[0]} ({type(v_ty[0])}) not list/set/dict"
                            )

                        for v_elem in c:
                            _wellformed_provenance_value(v_elem, v_ty[1])
                    else:
                        _wellformed_provenance_value(v, v_ty)

                return True
            except AssertionError as e:
                if strict:
                    raise e
                else:
                    return False

        @staticmethod
        def provenance_schema() -> dict[str, Any]:
            return {
                "cls": str,
                "bases": (list, str),
                "cls_code": (dict, str),
                "cls_extra": (dict, Any),
                "extra": (dict, Any),
            }

        # Note: equality comparisons are done based on serialized provenance
        def __eq__(self, other: Any) -> Any:
            if isinstance(other, ProvenanceBase.Metadata):
                return self.provenance() == other.provenance()
            elif self.wellformed_provenance(other):
                return self.provenance() == other
            else:
                return NotImplemented

        def __post_init__(self) -> None:
            self.__validate_cls()
            self.__validate_this()

        def __validate_cls(self) -> None:
            """Helper for __post_init__."""
            if not issubclass(self.cls, ProvenanceBase):
                raise ValueError(
                    f"{self.cls.__qualname__} must derive from Provenance.Base"
                )

            # Set self.cls_bases using validated self.cls
            object.__setattr__(
                self,
                "cls_bases",
                [
                    base
                    for base in self.cls.__bases__
                    if issubclass(base, ProvenanceBase)
                ],
            )

            self.__validate_attrs(
                self.cls,
                self.cls_code,
                "class-level code",
            )
            # Note: we don't do any validation for cls_extra

        def __validate_this(self) -> None:
            """Helper for __post_init__."""
            if self.this is None and self.extra is None:
                return
            elif self.this is not None and self.extra is not None:
                if not isinstance(self.this, self.cls):
                    raise ValueError(f"{self.this} not an instance of {self.cls}")
                # Note: we don't do any validation for extra
            else:
                raise ValueError(
                    "\n".join(
                        [
                            "no mixing None/Some:",
                        ]
                        + [
                            f"\t- {k} = {v}"
                            for k, v in {
                                "this": self.this,
                                "extra": self.extra,
                            }.items()
                        ]
                    )
                )

        def __validate_attrs[T](
            self,
            obj: ProvenanceBase | type[ProvenanceBase],
            attrs: dict[str, T],
            failure_msg: str,
            attr_lowerbound: type = object,
        ) -> None:
            """Helper to validate that attrs are bound on obj.

            Arguments:
              - obj: (instance of a) ProvenanceBase subclass
              - attrs: attrs to validate against obj
              - failure_msg: shared message to use for any validation failure

            Raises:
              ValueError, if any validation fails.
            """

            def _value_guard(v1: Any, v2: Any) -> str | None:
                if type(v1) is not type(v2):
                    return f"type: {type(v1)} is not {type(v2)}"
                if not issubclass(type(v1), attr_lowerbound):
                    return f"subclass: {type(v1)} not subclass of {attr_lowerbound}"
                if v1 != v2:
                    return f"value: {v1} != {v2}"
                return None

            def _bad_attr(exc_ty: type[Exception], reason: str) -> str:
                assert obj is self.cls or isinstance(obj, self.cls), (
                    "validation logic should have guarded this already"
                )
                raise exc_ty(f"{self.cls.__qualname__}: {reason}")

            for k, _v in attrs.items():
                if not hasattr(obj, k):
                    _bad_attr(AttributeError, k)
                # TODO: re-enable this if we can find a good way to test that
                # classmethods / bound methods are related correctly
                # guard_result = _value_guard(v, getattr(obj, k))
                # if guard_result is not None:
                #     _bad_attr(ValueError, guard_result)
