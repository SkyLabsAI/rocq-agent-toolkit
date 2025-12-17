"""Metaclass for building namespaces that expose types+utilities but can't be derived."""

from __future__ import annotations

from typing import Any


class FinalNamespaceMeta(type):
    def __new__(
        mcs: type[FinalNamespaceMeta],
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
        *,
        derive_from: dict[str, type] | None = None,
        **kwargs: Any,
    ) -> FinalNamespaceMeta:
        """Prevent deriving from classes that use metaclass=FinalNamespaceMeta.

        Arguments: beyond the default __new__ args (mcs, name, bases, namespace)
          - derive_from (dict[str, type]): attr names / types that should be
            derived from instead.

        Raises:
          - AttributeError: derive_from keys are missing from namespace
          - ValueError: derive_from is empty, derive_from/namespace value mismatch
          - TypeError: one of bases uses metaclass=FinalNamespaceMeta

        Returns: self, ready for initialization via __init__
        """

        for b in bases:
            if isinstance(b, FinalNamespaceMeta):
                if derive_from is None:
                    suggestion = ""
                else:
                    suggestion = "; prefer one of " + "".join(
                        [
                            "[",
                            ", ".join(
                                f"{b.__name__}.{attr_nm}"
                                for attr_nm in derive_from.keys()
                            ),
                            "]",
                        ]
                    )
                raise TypeError(
                    f"type '{b.__name__}' is not an acceptable base type{suggestion}"
                )

        if derive_from is None or len(derive_from) == 0:
            raise ValueError(f"{name} should provide a non-empty list for derive_from")

        for alias_nm, alias_ty in derive_from.items():
            if alias_nm not in namespace:
                raise AttributeError(
                    f"{mcs.__qualname__} derive_from: "
                    f"{alias_nm} not in namespace of {name}; "
                    f"namespace={namespace}"
                )
            elif alias_ty is not namespace[alias_nm]:
                raise ValueError(
                    f"{mcs.__qualname__} derive_from: "
                    f"expected {name}.{alias_nm} to have value {alias_ty.__name__}, "
                    f"but it is {namespace[alias_nm].__name__}; namespace={namespace}"
                )

        return type.__new__(mcs, name, bases, namespace, **kwargs)

    def __init__(
        mcs: FinalNamespaceMeta,
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
        *,
        derive_from: dict[str, type] | None = None,
        **kwargs: Any,
    ) -> None:
        type.__init__(mcs, name, bases, namespace, **kwargs)
