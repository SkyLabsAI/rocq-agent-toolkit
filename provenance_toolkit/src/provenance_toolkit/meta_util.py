"""Helpers for building ProvenanceMeta (cf. meta.py)."""

from __future__ import annotations

import inspect
import logging
from dataclasses import dataclass, field, fields
from typing import Any, ClassVar, Final, Literal, cast, final, overload

from .method_types import MethodTypes

logger = logging.getLogger(__name__)


@final
@dataclass(frozen=True)
class ProvenanceMetaTracking:
    ATTR_NAMESPACE: Final[ClassVar[str]] = "__ProvenanceMeta_TRACKING"

    # Note: set values / dict keys are all method names
    all_methods: set[str] = field(kw_only=True)
    all_staticmethods_compute_extra: set[str] = field(kw_only=True)
    all_classmethods_compute_extra: set[str] = field(kw_only=True)
    all_boundmethods_compute_extra: set[str] = field(kw_only=True)
    methods: set[str] = field(kw_only=True)
    staticmethods_compute_extra: set[str] = field(kw_only=True)
    classmethods_compute_extra: set[str] = field(kw_only=True)
    boundmethods_compute_extra: set[str] = field(kw_only=True)

    def __post_init__(self) -> None:
        for all_methods, methods in [
            (self.all_methods, self.methods),
            (
                self.all_staticmethods_compute_extra,
                self.staticmethods_compute_extra,
            ),
            (
                self.all_classmethods_compute_extra,
                self.classmethods_compute_extra,
            ),
            (
                self.all_boundmethods_compute_extra,
                self.boundmethods_compute_extra,
            ),
        ]:
            assert methods <= all_methods, (
                f"ProvenanceMeta error: methods not tracked transitively: "
                f"{methods - all_methods}"
            )

        all_methods_compute_extra: set[str] = set.union(
            set(self.all_staticmethods_compute_extra),
            set(self.all_staticmethods_compute_extra),
            set(self.all_staticmethods_compute_extra),
        )
        assert all_methods_compute_extra <= self.all_methods, (
            f"ProvenanceMeta error: untracked methods: "
            f"{all_methods_compute_extra - self.methods}"
        )

        methods_compute_extra: set[str] = set.union(
            set(self.staticmethods_compute_extra),
            set(self.staticmethods_compute_extra),
            set(self.staticmethods_compute_extra),
        )
        assert methods_compute_extra <= self.methods, (
            f"ProvenanceMeta error: untracked methods: "
            f"{methods_compute_extra - self.methods}"
        )

    @final
    @staticmethod
    def method_attr(attr: str) -> str:
        return f"{ProvenanceMetaTracking.ATTR_NAMESPACE}_{attr}"

    @final
    @staticmethod
    def validate_method_tracking_attrs(*attrs: str) -> None:
        field_nms = [f.name for f in fields(ProvenanceMetaTracking)]
        for attr in attrs:
            if attr not in field_nms:
                raise ValueError(f"ProvenaneMetaTracking: {attr} not in {field_nms}")

    @staticmethod
    @overload
    def lookup(
        klass: type,
        *,
        strict: Literal[True] = True,
    ) -> ProvenanceMetaTracking:
        """Lookup ProvenanceMetaTracking in cls.__dict__, raising error on failure."""

    @staticmethod
    @overload
    def lookup(
        klass: type,
        *,
        strict: bool | Literal[False],
    ) -> ProvenanceMetaTracking | None:
        """Attempt lookup ProvenanceMetaTracking in cls.__dict__."""

    @final
    @staticmethod
    def lookup(
        klass: type,
        *,
        strict: bool | Literal[True] | Literal[False] = True,
    ) -> ProvenanceMetaTracking | None:
        """Lookup ProvenanceMetaTracking in cls.__dict__.

        Returns:
          - ProvenanceMetaTracking for cls, if present
          - None, if ProvenanceMetaTracking is missing for cls and strict=False

        Raises:
          - ValueError, if ProvenanceMetaTracking is missing.
          - TypeError, if getattr(cls, ProvenanceMetaTracking.CLS_ATTR) is ill-typed
        """
        cls_attr = ProvenanceMetaTracking.ATTR_NAMESPACE

        if not hasattr(klass, cls_attr):
            msg = f"ProvenanceMeta error: {klass.__qualname__} missing {cls_attr}"
            if strict:
                raise ValueError(msg)
            else:
                logger.warning(msg)
                return None

        cls_tracking: Any = getattr(klass, cls_attr)
        if not isinstance(cls_tracking, ProvenanceMetaTracking):
            msg = " ".join(
                [
                    f"ProvenanceMeta error: {klass.__qualname__}.{cls_attr} ill typed;",
                    f"expected ProvenanceMetaTracking but got {type(cls_tracking)}",
                ]
            )
            if strict:
                raise TypeError(msg)
            else:
                logger.warning(msg)
                return None

        return cls_tracking


class ProvenanceMetaHelper(type):
    """Helper methods for ProvenanceMeta."""

    @final
    @classmethod
    def transitive_method_tracking(
        mcs: type[ProvenanceMetaHelper],
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
    ) -> None:
        """Perform transitive code tracking and mutate namespace as necessary."""
        attr_namespace = ProvenanceMetaTracking.ATTR_NAMESPACE

        assert attr_namespace not in namespace, (
            f"ProvenanceMeta error: {name} shouldn't define {attr_namespace} directly"
        )

        all_methods: set[str] = set()
        methods: set[str] = set()
        all_methods_compute_extra: dict[str, set[str]] = {
            "static": set(),
            "class": set(),
            "bound": set(),
        }
        methods_compute_extra: dict[str, set[str]] = {
            "static": set(),
            "class": set(),
            "bound": set(),
        }

        # Accumulate union of transitively tracked class-/instance-methods from bases
        for base in bases:
            if isinstance(base, mcs):
                tracking = ProvenanceMetaTracking.lookup(base)
                all_methods |= tracking.all_methods
                for kind in all_methods_compute_extra.keys():
                    all_methods_compute_extra[kind] |= getattr(
                        tracking,
                        f"all_{kind}methods_compute_extra",
                    )

        # For all_methods: if present in namespace and NOT explicitly tracked,
        # wrap as tracked
        for nm in all_methods:
            if nm not in namespace:
                continue  # not actually in this class
            methods.add(nm)

            value = namespace[nm]
            if not MethodTypes.is_method(value):
                raise ValueError(f"ProvenanceMeta error: {name} is not a method")

            extra_tracking_attrs: set[str] = (
                set()
                if hasattr(value, ProvenanceMetaTracking.method_attr("methods"))
                else {"methods"}
            )
            for kind in all_methods_compute_extra.keys():
                k = f"{kind}methods_compute_extra"

                # Only extend with missing attributes
                if (
                    not hasattr(value, ProvenanceMetaTracking.method_attr(k))
                    and nm in all_methods_compute_extra[kind]
                ):
                    extra_tracking_attrs.add(k)
            namespace[nm] = ProvenanceMetaHelper.track_method_as(
                value,
                extra_tracking_attrs=extra_tracking_attrs,
            )
            logger.debug(f"Auto-tracked override: {nm}")

        # Now, gather all explicitly tracked code in this class's namespace
        for nm, value in namespace.items():
            if not MethodTypes.is_method(value):
                continue

            if not hasattr(value, ProvenanceMetaTracking.method_attr("methods")):
                continue
            all_methods.add(nm)
            methods.add(nm)

            for kind, c in methods_compute_extra.items():
                namespaced_k = ProvenanceMetaTracking.method_attr(
                    f"{kind}methods_compute_extra"
                )
                if namespaced_k in value.__dict__:
                    c.add(nm)

        # finally, update all_methods with locally defined ones
        for kind, c in methods_compute_extra.items():
            all_methods_compute_extra[kind] |= c

        namespace[attr_namespace] = ProvenanceMetaTracking(
            all_methods=all_methods,
            all_staticmethods_compute_extra=all_methods_compute_extra["static"],
            all_classmethods_compute_extra=all_methods_compute_extra["class"],
            all_boundmethods_compute_extra=all_methods_compute_extra["bound"],
            methods=methods,
            staticmethods_compute_extra=methods_compute_extra["static"],
            classmethods_compute_extra=methods_compute_extra["class"],
            boundmethods_compute_extra=methods_compute_extra["bound"],
        )

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def track_method[O, **P, T](
        fn: MethodTypes.STATICMETHOD[P, T],
    ) -> MethodTypes.STATICMETHOD[P, T]:
        """Decorator: annotate staticmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method[O, **P, T](
        fn: MethodTypes.CLASSMETHOD[O, P, T],
    ) -> MethodTypes.CLASSMETHOD[O, P, T]:
        """Decorator: annotate classmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method[O, **P, T](
        fn: MethodTypes.BOUNDMETHOD[O, P, T],
    ) -> MethodTypes.BOUNDMETHOD[O, P, T]:
        """Decorator: annotate bound method fn with namespaced attrs."""

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def track_method_mk_extra_provenance[T](
        fn: MethodTypes.STATICMETHOD[[], T],
    ) -> MethodTypes.STATICMETHOD[[], T]:
        """Decorator: annotate staticmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method_mk_extra_provenance[O, T](
        fn: MethodTypes.CLASSMETHOD[O, [], T],
    ) -> MethodTypes.CLASSMETHOD[O, [], T]:
        """Decorator: annotate classmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method_mk_extra_provenance[O, T](
        fn: MethodTypes.BOUNDMETHOD[O, [], T],
    ) -> MethodTypes.BOUNDMETHOD[O, [], T]:
        """Decorator: annotate bound method fn with namespaced attrs."""

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def track_method_as[**P, T](
        fn: MethodTypes.STATICMETHOD[P, T],
        extra_tracking_attrs: set[str] | None = None,
    ) -> MethodTypes.STATICMETHOD[P, T]:
        """Decorator: annotate staticmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method_as[O, **P, T](
        fn: MethodTypes.CLASSMETHOD[O, P, T],
        extra_tracking_attrs: set[str] | None = None,
    ) -> MethodTypes.CLASSMETHOD[O, P, T]:
        """Decorator: annotate classmethod fn with namespaced attrs."""

    @staticmethod
    @overload
    def track_method_as[O, **P, T](
        fn: MethodTypes.BOUNDMETHOD[O, P, T],
        extra_tracking_attrs: set[str] | None = None,
    ) -> MethodTypes.BOUNDMETHOD[O, P, T]:
        """Decorator: annotate bound method fn with namespaced attrs."""

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters, and thinks that overload is the defn
    @final  # type: ignore[no-redef]
    @staticmethod
    def track_method[O, **P, T](
        fn: MethodTypes.METHOD[O, P, T],
    ) -> MethodTypes.METHOD[O, P, T]:
        return ProvenanceMetaHelper.track_method_as(fn)

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters, and thinks that overload is the defn
    @final  # type: ignore[no-redef]
    @staticmethod
    def track_method_mk_extra_provenance[O, T](
        fn: MethodTypes.METHOD[O, [], T],
    ) -> MethodTypes.METHOD[O, [], T]:
        """Decorator: register + use fn to compute extra provenance data.

        Works uniformly for staticmethods, classmethods and instance methods.
        Validates that fn is 0-arg (excluding self/cls, as relevant).
        """
        methods_compute_extra_attr: str
        fn_raw: MethodTypes.RAW_METHOD[O, [], T]

        # Note: we re-run the check in the conditional so that typecheckers
        # can propagate the `TypeIs` information into the branches.
        if MethodTypes.is_staticmethod(fn):
            fn_raw = fn.__func__
            methods_compute_extra_attr = "staticmethods_compute_extra"
        elif MethodTypes.is_classmethod(fn):
            fn_raw = fn.__func__
            methods_compute_extra_attr = "classmethods_compute_extra"
        elif MethodTypes.is_boundmethod(fn):
            fn_raw = fn
            methods_compute_extra_attr = "boundmethods_compute_extra"
        else:
            raise RuntimeError(f"{fn} is not a static/class/bound method")

        # Validate 0-arg (excluding self/cls)
        try:
            sig = inspect.signature(fn_raw)
            param_list = list(sig.parameters.values())
            # Should have exactly one parameter (self or cls)
            if MethodTypes.is_staticmethod(fn):
                if len(param_list) != 0:
                    raise ValueError(
                        f"@AgentProvenance.compute requires a 0-arg "
                        f"staticmethod, but {fn.__name__} has "
                        f"{len(param_list)} parameters"
                    )
            else:  # is_classmethod or is_boundmethod
                if len(param_list) != 1:
                    raise ValueError(
                        f"@AgentProvenance.compute requires a 0-arg "
                        f"classmethod/boundmethod (excluding self/cls), but "
                        f"{fn.__name__} has {len(param_list)} parameters"
                    )
                # The single parameter should be self or cls
                param = param_list[0]
                allowed_param_kinds = (
                    inspect.Parameter.POSITIONAL_ONLY,
                    inspect.Parameter.POSITIONAL_OR_KEYWORD,
                    inspect.Parameter.KEYWORD_ONLY,
                )
                if param.kind not in allowed_param_kinds:
                    raise ValueError(
                        f"@AgentProvenance.compute: invalid parameter kind "
                        f"for {fn.__name__}; {param.kind} not "
                        f" in {allowed_param_kinds}"
                    )
        except (ValueError, TypeError, OSError) as e:
            # inspect.signature can fail in some cases (e.g.,
            # C extensions, binary distributions)
            logger.warning(
                f"Could not validate 0-arg requirement for {fn.__name__}: {e}"
            )

        assert MethodTypes.is_method(fn)
        return ProvenanceMetaHelper.track_method_as(
            # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
            # same number of type parameters, and thinks that overload is the defn
            cast(MethodTypes.METHOD[O, [], T], fn),  # type: ignore[arg-type]
            extra_tracking_attrs={methods_compute_extra_attr},
        )

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters, and thinks that overload is the defn
    @final  # type: ignore[no-redef]
    @staticmethod
    def track_method_as[O, **P, T](
        fn: MethodTypes.METHOD[O, P, T],
        extra_tracking_attrs: set[str] | None = None,
    ) -> MethodTypes.METHOD[O, P, T]:
        """Decorator: annotate fn with namespaced attrs.

        Works uniformly for staticmethods, classmethods and instance methods.
        """
        assert MethodTypes.is_method(fn)

        tracking_attrs = {"methods", *(extra_tracking_attrs or set())}
        ProvenanceMetaTracking.validate_method_tracking_attrs(*tracking_attrs)

        for attr in tracking_attrs:
            object.__setattr__(
                fn,
                ProvenanceMetaTracking.method_attr(attr),
                None,
            )

        return fn
