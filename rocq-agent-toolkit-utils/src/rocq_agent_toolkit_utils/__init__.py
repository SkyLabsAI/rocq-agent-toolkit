from . import json, objects

# TODOs:
# 1) env.py:
#    - predicates:
#      + dev/dbg?
# 2) pydantic.py:
#    - mixins / tweaks to BaseModel+Field:
#      + prevent "private" data from being dumped

__all__ = [
    "json",
    "objects",
]
