# Search

The search module provides generic search infrastructure for agents working on MDPs.
It is especially focused on MDPs with infinite action spaces.

The module contains the following concepts:
* [Strategies](strategy.py) capture classes of related actions. For example, in proof assistant context, a single strategy might encapsulate different approaches to synthesizing loop invariants.
* [Actions](action.py) capture searches for individual actions that can be taken in the MDP. These actions are allowed to fail and are also allowed to take multiple steps within the underlying MDP. This can be particulary important within the context of theorem proving because it allows an `Action` to refine the actual tactic combination that is run, e.g. if the original proposal does not type check, then an iteration can try to fix the typing errors.

## The Rocq Instantiation
The [rocq/](rocq/) directory contains several building blocks that might be useful for connecting these to Rocq.
