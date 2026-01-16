from logging import Logger
from typing import Any

from observability.logging import StructuredLogger


def _info(
    logger: Logger | StructuredLogger,
    *,
    key: str,
    **kwargs: Any,
) -> None:
    if isinstance(logger, StructuredLogger):
        logger.info(key, **kwargs)
    else:
        logger.info(key, extra=kwargs)


class TraceRocqTacInferenceMixin:
    """Mixin for classes that trace inference of Rocq tactics."""

    def log_rocq_tactic_prediction(
        self,
        logger: Logger | StructuredLogger,
        *,
        # Note: we could use a richer type for source
        source: str,
        tactic: str,
        explanation: str,
        probability: float | None = None,
        extra: dict[str, Any] | None = None,
    ) -> None:
        if extra is None:
            extra = {}

        _info(
            logger,
            key="Tactic Prediction Explanation",
            tactic_prediction_source=source,
            tactic_prediction_explanation=explanation,
            **extra,
        )

        _info(
            logger,
            key="Tactic Prediction Tactic",
            tactic=tactic,
        )

        if probability is not None:
            _info(
                logger,
                key="Tactic Prediction Probability",
                probability=str(probability),
            )


class TraceRocqTacApplicationMixin:
    """Mixin for classes that trace interactions with Rocq."""

    def log_rocq_tactic_failure(
        self,
        logger: Logger | StructuredLogger,
        *,
        pre_state: str | dict[str, Any] | None = None,
        tactic: str,
        error: str | Exception,
    ) -> None:
        self.log_rocq_pf_state_pre(logger, state=pre_state)
        self.log_rocq_tactic_application(
            logger,
            tactic=tactic,
            error=error,
        )

    def log_rocq_tactic_success(
        self,
        logger: Logger | StructuredLogger,
        *,
        pre_state: str | dict[str, Any] | None = None,
        tactic: str,
        post_state: str | dict[str, Any] | None = None,
    ) -> None:
        self.log_rocq_pf_state_pre(logger, state=pre_state)
        self.log_rocq_tactic_application(logger, tactic=tactic)
        self.log_rocq_pf_state_post(logger, state=post_state)

    def log_rocq_tactic_application(
        self,
        logger: Logger | StructuredLogger,
        *,
        tactic: str,
        error: str | Exception | None = None,
    ) -> None:
        _info(
            logger,
            key="Tactic Application",
            tactic_application=tactic,
        )

        if error is not None:
            _info(
                logger,
                key="Tactic Application Status",
                status="Failure",
                error_msg=str(error),
            )
        else:
            _info(logger, key="Tactic Application Status", status="Success")

    def log_rocq_pf_state_pre(
        self,
        logger: Logger | StructuredLogger,
        *,
        state: str | dict[str, Any] | None = None,
    ) -> None:
        if state is not None:
            _info(
                logger,
                key="Tactic Pre State",
                state=state,
            )

    def log_rocq_pf_state_post(
        self,
        logger: Logger | StructuredLogger,
        *,
        state: str | dict[str, str] | None = None,
    ) -> None:
        if state is not None:
            _info(
                logger,
                key="Tactic Post State",
                pf_state_pre=state,
            )
