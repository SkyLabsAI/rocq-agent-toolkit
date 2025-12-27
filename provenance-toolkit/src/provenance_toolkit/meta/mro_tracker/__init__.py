"""MROTracker: composable & extensible inheritance hierarchy tracking.

The `provenance_toolkit` makes it simple to compose:
- Python code-provenance (this package):
  + fine-grained & stable: track only what's relevant; minimize churn
  + lightweight hooks: decorators + metaclass injections for derivers
  + extension points: overrideable interfaces w/reasonable defaults
- data-provenance:
  + lightweight hooks (this package): decorators + metaclass injections for derivers
  + extension points: your favorite data-provenance package

Information is tracked at both the class and instance levels, with the goal
of disambiguating code changes over time. Inheritance information (i.e. bases)
is tracked for all objects in the inheritance hierarchy. Additionally,
clients can opt-in to additional method/data tracking using MROTrackerMeta
and associated decorators.

The core class is MROTracker, a namespace class consisting of:
- MROTracker.Datum: class-/instance-local inheritance information
- MROTracker.Data: whole-hierarchy inheritance information
- MROTracker.Meta: metaclass for managing automatic inheritance hierarchy tracking
- decorators for hooking into the provenance autogeneration mechanism:
  + MROTracker.track: mark a method s.t. it /and/ all overrides
    in derivers are automatically tracked
  + MROTracker.compute:  register + use the zero-argument method to dynamically
    compute extra provenance information
- factory methods for producing whole hierarchy provenance information (MROTracker.Data):
  + MROTracker.build(compute: bool = True): whole-hierarchy inheritance information;
    if compute=True, additionally gather runtime data by execution specially-tracked
    methods.

At a high level the MROTrackerData can be thought of like a hash of the key parts
of a given class/instance. MROTracker.Meta is designed to provide reasonable
defaults in most cases so that derivers only have to add minimal annotations
in order to get reasonable behavior.

Note: whole hierarchy provenance information is a map from classes
in the hierarchy to class-/instance-local information.

See mro_tracker.py for more details.
"""

from typing import TypeAlias

from ..final_namespace import FinalNamespaceMeta
from .data import MROTrackerData, MROTrackerDatum
from .decorator import MROTrackerDecorator
from .meta import MROTrackerMeta


class MROTracker(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Decorator": MROTrackerDecorator,
        "Meta": MROTrackerMeta,
    },
):
    Datum: TypeAlias = MROTrackerDatum  # noqa: UP040
    Data: TypeAlias = MROTrackerData  # noqa: UP040
    Decorator: TypeAlias = MROTrackerDecorator  # noqa: UP040
    Meta: TypeAlias = MROTrackerMeta  # noqa: UP040


__all__: list[str] = [
    "MROTracker",
]
