"""
Workflow step extractor for pipeline and workflow operations.

This extractor understands workflow steps and pipeline operations, extracting
workflow-specific attributes for tracing. It works with any workflow system.
"""

from typing import Any, Callable, Dict, Optional, Tuple

from .base import AttributeExtractor


class WorkflowExtractor(AttributeExtractor):
    """
    Extractor for workflow steps and pipeline operations.

    Supports:
    - LangGraph workflow steps
    - Data pipeline steps
    - Business workflow steps
    - State machine transitions
    - Any workflow or pipeline operation

    Example usage:
        @trace(extractor="workflow", workflow_type="user_onboarding")
        def validate_email(state):
            state['email_valid'] = validate(state['email'])
            return state

        @trace(extractor=WorkflowExtractor(step_name="process_payment",
                    workflow_type="checkout"))
        def process_payment_step(order_data):
            return payment_service.charge(order_data)
    """

    def __init__(
        self,
        workflow_type: Optional[str] = None,
        step_name: Optional[str] = None,
        include_state: bool = False,
        include_input: bool = True,
        include_output: bool = True,
        max_data_length: int = 1000,
        state_arg: str = "state",
    ):
        """
        Initialize workflow extractor.

        Args:
            workflow_type: Type of workflow ("user_onboarding", "data_pipeline", etc.)
            step_name:
                Override step name (auto-detected from function name if not provided)
            include_state: Whether to include full state data in spans
            include_input: Whether to include input data
            include_output: Whether to include output data
            max_data_length: Maximum length for data attributes
            state_arg: Name of the state argument in function signature
        """
        self.workflow_type = workflow_type
        self.step_name = step_name
        self.include_state = include_state
        self.include_input = include_input
        self.include_output = include_output
        self.max_data_length = max_data_length
        self.state_arg = state_arg

    def extract_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Extract workflow attributes from function call."""
        attrs = {
            "workflow.step.name": self.step_name or func.__name__,
        }

        # Add workflow type
        if self.workflow_type:
            attrs["workflow.type"] = self.workflow_type

        # Try to extract workflow information from state
        state = self._find_state(args, kwargs)
        if state:
            workflow_attrs = self._extract_workflow_info(state)
            attrs.update(workflow_attrs)

        # Add step timing information
        attrs["workflow.step.type"] = "function"

        return attrs

    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Generate span name for workflow step."""
        step_name = self.step_name or func.__name__

        if self.workflow_type:
            return f"workflow.{self.workflow_type}.{step_name}"
        else:
            return f"workflow.{step_name}"

    def get_metrics_labels(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, str]:
        """Generate metrics labels for workflow operations."""
        labels = {
            "operation": func.__name__,
            "step": self.step_name or func.__name__,
        }

        if self.workflow_type:
            labels["workflow_type"] = self.workflow_type

        # Try to extract workflow ID for grouping
        state = self._find_state(args, kwargs)
        if state:
            workflow_id = self._extract_workflow_id(state)
            if workflow_id:
                # Use a prefix of the workflow ID to avoid high cardinality
                labels["workflow_prefix"] = (
                    workflow_id[:8] if len(workflow_id) > 8 else workflow_id
                )

        return labels

    def _find_state(self, args: Tuple, kwargs: Dict[str, Any]) -> Any:
        """Find the state object in function arguments."""
        # Check kwargs first
        if self.state_arg in kwargs:
            return kwargs[self.state_arg]

        # Check first argument (common pattern)
        if args:
            first_arg = args[0]
            # Skip 'self' if this is a method
            if (
                hasattr(first_arg, "__dict__")
                and hasattr(first_arg, "__class__")
                and len(args) > 1
            ):
                return args[1]
            else:
                return first_arg

        return None

    def _extract_workflow_info(self, state: Any) -> Dict[str, Any]:
        """Extract workflow information from state object."""
        attrs = {}

        # Try to extract workflow ID
        workflow_id = self._extract_workflow_id(state)
        if workflow_id:
            attrs["workflow.id"] = workflow_id

        # Try to extract workflow execution ID (different from workflow definition ID)
        execution_id = self._extract_execution_id(state)
        if execution_id:
            attrs["workflow.execution.id"] = execution_id

        # Try to extract step sequence/index
        step_index = self._extract_step_index(state)
        if step_index is not None:
            attrs["workflow.step.index"] = str(step_index)

        # Try to extract workflow status
        status = self._extract_workflow_status(state)
        if status:
            attrs["workflow.status"] = status

        # Extract additional workflow metadata
        metadata = self._extract_workflow_metadata(state)
        if metadata:
            attrs.update(metadata)

        return attrs

    def _extract_workflow_id(self, state: Any) -> Optional[str]:
        """Extract workflow ID from state."""
        if isinstance(state, dict):
            # Try common field names
            for field in ["workflow_id", "id", "workflow_uuid", "uuid"]:
                if field in state and state[field]:
                    return str(state[field])

        # Try object attributes
        for attr in ["workflow_id", "id", "workflow_uuid", "uuid"]:
            if hasattr(state, attr):
                value = getattr(state, attr)
                if value:
                    return str(value)

        return None

    def _extract_execution_id(self, state: Any) -> Optional[str]:
        """Extract workflow execution ID from state."""
        if isinstance(state, dict):
            for field in ["execution_id", "run_id", "session_id"]:
                if field in state and state[field]:
                    return str(state[field])

        for attr in ["execution_id", "run_id", "session_id"]:
            if hasattr(state, attr):
                value = getattr(state, attr)
                if value:
                    return str(value)

        return None

    def _extract_step_index(self, state: Any) -> Optional[int]:
        """Extract step index/sequence number from state."""
        if isinstance(state, dict):
            for field in ["step_index", "current_step", "step_number"]:
                if field in state and isinstance(state[field], int):
                    return int(state[field])

        for attr in ["step_index", "current_step", "step_number"]:
            if hasattr(state, attr):
                value = getattr(state, attr)
                if isinstance(value, int):
                    return value

        return None

    def _extract_workflow_status(self, state: Any) -> Optional[str]:
        """Extract workflow status from state."""
        if isinstance(state, dict):
            for field in ["status", "state", "phase"]:
                if field in state and state[field]:
                    return str(state[field])

        for attr in ["status", "state", "phase"]:
            if hasattr(state, attr):
                value = getattr(state, attr)
                if value:
                    return str(value)

        return None

    def _extract_workflow_metadata(self, state: Any) -> Dict[str, Any]:
        """Extract additional workflow metadata."""
        attrs = {}

        if isinstance(state, dict):
            # Look for common metadata fields
            metadata_fields = {
                "user_id": "workflow.user_id",
                "tenant_id": "workflow.tenant_id",
                "version": "workflow.version",
                "environment": "workflow.environment",
                "priority": "workflow.priority",
                "tags": "workflow.tags",
                "source": "workflow.source",
                "created_at": "workflow.created_at",
                "started_at": "workflow.started_at",
            }

            for field, attr_name in metadata_fields.items():
                if field in state and state[field]:
                    value = state[field]
                    if isinstance(value, (str, int, float, bool)):
                        attrs[attr_name] = str(value)[: self.max_data_length]
                    elif isinstance(value, list):
                        attrs[attr_name] = str(value)[: self.max_data_length]

        return attrs
