Goal-To-JSON
===============

Tactic to extract the Rocq goal to a JSON object.

Usage
-----

```coq
Require Import skylabs_ai.extractors.goal_to_json.basic.goal_util.

Goal True.
Proof. goal_to_json. trivial. Qed.
```
