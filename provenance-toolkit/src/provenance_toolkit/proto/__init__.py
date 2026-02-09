"""Extension Point: protocol for computing class and instance provenance data.

`WithProvenance` requires both class and instance provenance data to be computed.
`WithClassProvenance` and `WithInstanceProvenance` can be used separately.

The core API is:
- `checksum(self)`/`cls_checksum(cls) -> str:
   Compute a semi-stable instance/class checksum for the provenance data.
- `checksums(self)`/`cls_checksums(cls)` -> Mapping[type[WithInstanceProvenance], str] / Mapping[type[WithClassProvenance], str]:
   Compute the instance/class checksums of provenance data, keyed by the type of the
   class that computed it.
- `provenance(self)`/`cls_provenance(cls)` -> Mapping[type[WithInstanceProvenance], ProvenanceT] / Mapping[type[WithClassProvenance], ProvenanceT]:
   Compute instance/class provenance data, keyed by the type of the class that
   computed it.

Each class that directly provides a concrete override for `compute_provenance` and/or
`compute_cls_provenance` -- and has no parent class that also concretely overrides it -- is
automatically registered as the base of a unique kind of instance/class provenance data.

During provenance computation, instance/class provenance data is computed once for each
of these unique kinds by calling the most derived implementation of that kind in the MRO.
This allows both overriding and extending instance/class provenance data.

Note: cf. provenance-toolkit/src/examples/ for more details.
"""

from .base import ComputeChecksumProvenanceT, ProvenanceT
from .for_class import WithClassProvenance
from .for_instance import WithInstanceProvenance

__all__: list[str] = [
    # base.py
    "ComputeChecksumProvenanceT",
    "ProvenanceT",
    # for_class.py
    "WithClassProvenance",
    # for_instance.py
    "WithInstanceProvenance",
    # __init__.py
    "WithProvenance",
]


class WithProvenance(WithClassProvenance, WithInstanceProvenance):
    """Extension Point: protocol for computing class and instance provenance data.

    See WithClassProvenance and WithInstanceProvenance for more details."""
