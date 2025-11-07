from rocq_pipeline.proof_state.goal_parts import RocqGoalParts


class RocqGoal:
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
    def parts(self) -> RocqGoalParts:
        return self._parts

    def wellformed(self) -> bool:
        return self.parts.wellformed()
