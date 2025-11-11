from rocq_pipeline.proof_state.goal_parts import RocqGoalParts


class RocqGoal:
    """Single Rocq goal, consisting of structured goal parts.

    This class may contain mutable state and should collect
    all utilities that can be expressed at the level of structured
    Rocq goals.
    """

    # This tells the classmethod 'from_str' which Parts dataclass to use.
    # Subclasses will override this.
    PartsDataclass: type[RocqGoalParts] = RocqGoalParts

    def __init__(self, parts: RocqGoalParts) -> None:
        if not isinstance(parts, RocqGoalParts):
            raise ValueError(
                f"Expected parts (RocqGoalParts), but got ({type(parts)})"
            )
        self._parts = parts

    @property
    def raw_str(self) -> str:
        return self._parts.rocq_goal_raw

    @property
    def parts(self) -> RocqGoalParts:
        return self._parts

    def wellformed(self) -> bool:
        return self.parts.wellformed()
