"""Example usage of Provenance.Reflect for automatically including annotated data members.

This demonstrates how to use Annotated[T, Provenance.Reflect.Field] to mark class and instance
fields that should be automatically included in provenance computation."""

from __future__ import annotations

from typing import Annotated, Final

from provenance_toolkit import Provenance
from provenance_toolkit.provenance.reflect import ReflectProvenanceData


class Config(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """Example configuration class with provenance."""

    pass


class MyAgent(
    Provenance.ClassIdentity, Provenance.Version, Provenance.Reflect, VERSION="1.0.0"
):
    """Example agent class using Reflect provenance."""

    # Class variable with best-effort auto-detection (no ClassVar wrapper needed)
    # Using Field to mark the field for reflection
    cfg: Final[Annotated[Config, Provenance.Reflect.Field]] = Config()

    # With static method transform
    @staticmethod
    def normalize(val: float) -> float:
        """Normalize a float value."""
        return round(val, 2)

    normalized: Final[
        Annotated[float, Provenance.Reflect.Field(transform=normalize)]
    ] = 0.95123

    # Instance field annotation (set in __init__)
    model: Annotated[str, Provenance.Reflect.Field(transform=lambda x: f"model_{x}")]

    def __init__(self, model_name: str) -> None:
        """Initialize agent with model name."""
        super().__init__()
        # Instance field with explicit transform
        self.model = model_name


if __name__ == "__main__":
    from pprint import pprint

    print("=" * 60)
    print("Class Provenance")
    print("=" * 60)
    print(f"MyAgent.cls_checksum() = {MyAgent.cls_checksum()}")
    print("MyAgent.cls_checksums()")
    pprint(MyAgent.cls_checksums())
    print("MyAgent.cls_provenance()")
    pprint(MyAgent.cls_provenance())

    # Get reflect provenance data
    cls_prov = MyAgent.cls_provenance()
    from provenance_toolkit.provenance.reflect import WithReflectProvenance

    reflect_prov = cls_prov[WithReflectProvenance]
    assert isinstance(reflect_prov, ReflectProvenanceData)
    print("\nReflect data:")
    pprint(reflect_prov.data)
    print(f"\nReflect serialized: {reflect_prov.stable_serialize()}")

    print("\n" + "=" * 60)
    print("Instance Provenance")
    print("=" * 60)
    agent = MyAgent("gpt-4")
    print(f"agent.checksum() = {agent.checksum()}")
    print("agent.checksums()")
    pprint(agent.checksums())
    print("agent.provenance()")
    pprint(agent.provenance())

    # Get reflect provenance data
    inst_prov = agent.provenance()
    reflect_prov_inst = inst_prov[WithReflectProvenance]
    assert isinstance(reflect_prov_inst, ReflectProvenanceData)
    print("\nReflect data:")
    pprint(reflect_prov_inst.data)
    print(f"\nReflect serialized: {reflect_prov_inst.stable_serialize()}")
