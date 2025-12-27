### Introduction

`provenance-toolkit` enables you to track rich structural provenance & signatures at the class-/instance-level:
- rich structural provenance: extensible Python types for accumulating information related to the identity of classes/instances at each point in the inheritance hierarchy
- signatures: strings, which should be semi-stable and pseudo-unique so that they may be used as primary keys to track and disambiguate class/instance usage over time

### Features

cf. [`src/provenance_toolkit/__init__.py`](./src/provenance_toolkit/__init__.py) & [`examples/`](./examples)

### Future Work

- [improve usability / ergonomics for clients by introducing decorator (factory) hook points for extending structural provenance](https://github.com/SkyLabsAI/rocq-agent-toolkit/issues/16)
- investigate using the [W3C PROV data model](https://www.w3.org/TR/prov-dm/) ([python module: prov](https://github.com/trungdong/prov)) for rich provenance information
