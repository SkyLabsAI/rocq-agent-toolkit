import logging

from rocq_pipeline.proof_state.goal import IrisGoal, RocqGoal
from rocq_pipeline.proof_state.goal_parts import into_GoalParts
from rocq_pipeline.proof_state.parse.iris import into_IrisGoalParts
from rocq_pipeline.proof_state.parse.rocq import into_RocqGoalParts

logger = logging.getLogger(__name__)


class GoalParserRegistry:
    """Registry for goal type parsers."""

    _registry: dict[type[RocqGoal], into_GoalParts] = {}

    @classmethod
    def register(
        cls,
        goal_type: type[RocqGoal],
        parser_function: into_GoalParts,
    ) -> None:
        """Manually register a parser function for a goal type.

        Args:
            goal_type: The goal class (must be a subclass of RocqGoal)
            parser_function: function matching into_GoalParts protocol
        """
        if not issubclass(goal_type, RocqGoal):
            raise ValueError(f"{goal_type} must be a subclass of RocqGoal")
        cls._registry[goal_type] = parser_function

    @classmethod
    def get_parser(cls, goal_type: type[RocqGoal]) -> into_GoalParts | None:
        """Get the parser function for a goal type.

        Checks both the explicit registry and class attributes (ParserFunction).

        Args:
            goal_type: The goal class to get a parser for

        Returns:
            The parser function, or None if not found
        """
        # First check explicit registry
        if goal_type in cls._registry:
            return cls._registry[goal_type]

        return None

    @classmethod
    def has_parser(cls, goal_type: type[RocqGoal]) -> bool:
        """Check if a parser is registered for the given goal type."""
        return cls.get_parser(goal_type) is not None


# Register built-in parsers
GoalParserRegistry.register(RocqGoal, into_RocqGoalParts)
GoalParserRegistry.register(IrisGoal, into_IrisGoalParts)


def register_goal_parser(
    goal_type: type[RocqGoal],
    parser_function: into_GoalParts,
) -> None:
    """Register a parser function for a goal type.

    This is the public API for clients to register custom goal parsers.

    Example:
        ```python
        from rocq_pipeline.proof_state.parse.proof_state import register_goal_parser
        from rocq_pipeline.proof_state.goal import RocqGoal
        from rocq_pipeline.proof_state.goal_parts import RocqGoalParts

        def my_custom_parser(
            goal: str,
            *,
            rocq_rel_goal_num: int,
            rocq_shelved_cnt: int,
            rocq_admit_cnt: int,
            rocq_goal_id: int | None = None,
            is_concl_only: bool = False,
            silent: bool = False,
        ) -> MyCustomGoalParts:
            # ... parsing logic ...
            return MyCustomGoalParts(...)

        register_goal_parser(MyCustomGoal, my_custom_parser)
        ```

    Args:
        goal_type: The goal class (must be a subclass of RocqGoal)
        parser_function: Function that parses a goal string into GoalParts
    """
    GoalParserRegistry.register(goal_type, parser_function)


def str_into_Goal(
    goal_str: str,
    *,
    goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    rocq_rel_goal_num: int,
    rocq_shelved_cnt: int,
    rocq_admit_cnt: int,
    rocq_goal_id: int | None = None,
) -> RocqGoal:
    if not issubclass(goal_ty_upperbound, RocqGoal):
        raise RuntimeError(f"{goal_ty_upperbound} not a subclass of RocqGoal")

    goal = _into_Goals.parse_goal_string(
        goal_str,
        goal_ty_upperbound=goal_ty_upperbound,
        rocq_rel_goal_num=rocq_rel_goal_num,
        rocq_shelved_cnt=rocq_shelved_cnt,
        rocq_admit_cnt=rocq_admit_cnt,
        rocq_goal_id=rocq_goal_id,
    )
    if goal is not None and goal.wellformed():
        return goal
    else:
        raise RuntimeError(
            f"Goal parsing failure (upperbound {goal_ty_upperbound.__name__}):\n{goal_str}"
        )


class _into_Goals:
    @staticmethod
    def parse_goal_string(
        goal_str: str,
        *,
        goal_ty_upperbound: type[RocqGoal],
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int,
        rocq_admit_cnt: int,
        rocq_goal_id: int | None = None,
        is_concl_only: bool = False,
    ) -> RocqGoal | None:
        """
        Try to parse a single goal string using the MRO of goal_ty_upperbound.
        Start with the most specific type and falls back to the most general.
        """
        for cls in goal_ty_upperbound.__mro__:
            if not issubclass(cls, RocqGoal):
                continue

            # Get parser from registry (supports both manual and automatic registration)
            parser = GoalParserRegistry.get_parser(cls)
            if parser is None:
                logger.debug("Failed to find goal parser for {cls.__name__}")
                continue

            structured_goal = cls(
                parser(
                    goal_str,
                    rocq_rel_goal_num=rocq_rel_goal_num,
                    rocq_shelved_cnt=rocq_shelved_cnt,
                    rocq_admit_cnt=rocq_admit_cnt,
                    rocq_goal_id=rocq_goal_id,
                    is_concl_only=is_concl_only,
                    silent=True,  # Silence warnings during fallback
                )
            )

            if structured_goal.wellformed():
                return structured_goal

        # Warning if no parser worked
        print(
            f"Warning: Could not parse goal {rocq_rel_goal_num}:\n{goal_str[:200]}..."
        )
        return None
