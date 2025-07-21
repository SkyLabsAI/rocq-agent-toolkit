"""
LangChain/LangGraph operation extractor.

This extractor understands LangChain chains, LangGraph workflows, and LLM operations,
extracting standard AI/ML attributes for tracing. It works with any LangChain-based
application including custom chains and workflows.
"""

from typing import Any, Dict, Callable, Tuple, Optional

from opentelemetry import propagate
from opentelemetry.context import Context

from .base import AttributeExtractor

try:
    from langgraph.types import Command
    LANGGRAPH_AVAILABLE = True
except ImportError:
    LANGGRAPH_AVAILABLE = False


class LangChainExtractor(AttributeExtractor):
    """
    Extractor for LangChain/LangGraph operations.
    
    Supports:
    - LangChain chains and runnables
    - LangGraph workflows and state graphs
    - LLM and chat model operations
    - Agent and tool operations
    - Custom LangChain components
    
    Example usage:
        @trace(extractor="langchain")
        def chat_with_llm(prompt):
            return llm.invoke(prompt)
            
        @trace(extractor=LangChainExtractor(chain_type="conversation", include_token_usage=True))
        def conversation_chain(user_input):
            return chain.invoke({"input": user_input})
            
        @trace(extractor="langchain", workflow_type="customer_support")
        def support_workflow_step(state):
            # LangGraph step
            return process_customer_query(state)
    """
    
    def __init__(self, 
                 chain_type: Optional[str] = None,
                 workflow_type: Optional[str] = None,
                 include_inputs: bool = True,
                 include_outputs: bool = True,
                 include_token_usage: bool = True,
                 include_model_info: bool = True,
                 max_input_length: int = 1000,
                 max_output_length: int = 1000):
        """
        Initialize LangChain extractor.
        
        Args:
            chain_type: Type of LangChain operation ("conversation", "retrieval", "agent", etc.)
            workflow_type: Type of workflow for LangGraph operations
            include_inputs: Whether to include input data in spans
            include_outputs: Whether to include output data in spans  
            include_token_usage: Whether to include token usage information
            include_model_info: Whether to include model information
            max_input_length: Maximum length for input attributes
            max_output_length: Maximum length for output attributes
        """
        self.chain_type = chain_type
        self.workflow_type = workflow_type
        self.include_inputs = include_inputs
        self.include_outputs = include_outputs
        self.include_token_usage = include_token_usage
        self.include_model_info = include_model_info
        self.max_input_length = max_input_length
        self.max_output_length = max_output_length
    
    def extract_attributes(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract LangChain attributes from function call."""
        attrs = {
            "langchain.operation": func.__name__,
            "langchain.operation_type": self._determine_operation_type(func, args, kwargs),
        }
        
        # Add chain type if specified
        if self.chain_type:
            attrs["langchain.chain_type"] = self.chain_type
        
        # Add workflow type if specified
        if self.workflow_type:
            attrs["langchain.workflow_type"] = self.workflow_type
            attrs["workflow.type"] = self.workflow_type  # Also use standard workflow attribute
        
        # Extract component information
        component_info = self._extract_component_info(func, args, kwargs)
        if component_info:
            attrs.update(component_info)
        
        # Extract input information if requested
        if self.include_inputs:
            input_info = self._extract_input_info(args, kwargs)
            if input_info:
                attrs.update(input_info)
        
        # Try to detect LangGraph state if this looks like a workflow step
        if self._is_langgraph_step(args, kwargs):
            langgraph_attrs = self._extract_langgraph_attributes(args, kwargs)
            attrs.update(langgraph_attrs)
        
        return attrs
    
    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Generate span name for LangChain operation."""
        operation_type = self._determine_operation_type(func, args, kwargs)
        
        if self.workflow_type:
            return f"langchain.workflow.{self.workflow_type}.{func.__name__}"
        elif self.chain_type:
            return f"langchain.chain.{self.chain_type}.{func.__name__}"
        elif operation_type != "unknown":
            return f"langchain.{operation_type}.{func.__name__}"
        else:
            return f"langchain.{func.__name__}"
    
    def get_metrics_labels(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, str]:
        """Generate metrics labels for LangChain operations."""
        labels = {
            "operation": func.__name__,
            "operation_type": self._determine_operation_type(func, args, kwargs),
            "langchain_component": "true",
        }
        
        # Add chain type if available
        if self.chain_type:
            labels["chain_type"] = self.chain_type
        
        # Add workflow type if available
        if self.workflow_type:
            labels["workflow_type"] = self.workflow_type
        
        return labels
    
    def extract_error_attributes(self, func: Callable, args: Tuple, kwargs: Dict[str, Any], 
                               exception: Exception) -> Dict[str, Any]:
        """Extract LangChain-specific error attributes."""
        attrs = super().extract_error_attributes(func, args, kwargs, exception)
        
        # Add LangChain-specific error context
        attrs["langchain.error_type"] = type(exception).__name__
        
        # Check for common LangChain exceptions
        if hasattr(exception, 'llm_output'):
            attrs["langchain.llm_output"] = str(exception.llm_output)[:500]
        
        return attrs
    
    def _determine_operation_type(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Determine the type of LangChain operation."""
        func_name = func.__name__.lower()
        
        # Check for common LangChain operation patterns
        if any(pattern in func_name for pattern in ['llm', 'chat', 'model']):
            return "llm"
        elif any(pattern in func_name for pattern in ['chain', 'runnable']):
            return "chain"
        elif any(pattern in func_name for pattern in ['agent', 'tool']):
            return "agent"
        elif any(pattern in func_name for pattern in ['retrieval', 'vector', 'search']):
            return "retrieval"
        elif any(pattern in func_name for pattern in ['workflow', 'graph', 'state']):
            return "workflow"
        else:
            return "unknown"
    
    def _extract_component_info(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract information about LangChain components."""
        attrs = {}
        
        # Try to detect the type of component being used
        if args:
            first_arg = args[0]
            if hasattr(first_arg, '__class__'):
                class_name = first_arg.__class__.__name__
                attrs["langchain.component_class"] = class_name
                
                # Extract model information if available
                if self.include_model_info and hasattr(first_arg, 'model_name'):
                    attrs["langchain.model_name"] = first_arg.model_name
                elif self.include_model_info and hasattr(first_arg, 'model'):
                    attrs["langchain.model"] = str(first_arg.model)
        
        return attrs
    
    def _extract_input_info(self, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract input information for the operation."""
        attrs = {}
        
        # Look for common input patterns
        if args and len(args) > 0:
            input_data = args[0] if args else None
        elif 'input' in kwargs:
            input_data = kwargs['input']
        elif 'prompt' in kwargs:
            input_data = kwargs['prompt']
        elif 'query' in kwargs:
            input_data = kwargs['query']
        else:
            input_data = None
        
        if input_data is not None:
            # Handle different input types
            if isinstance(input_data, str):
                attrs["langchain.input"] = self._truncate_string(input_data, self.max_input_length)
                attrs["langchain.input_length"] = len(input_data)
            elif isinstance(input_data, dict):
                attrs["langchain.input_type"] = "dict"
                attrs["langchain.input_keys"] = list(input_data.keys())
                # Try to get text content from common keys
                for key in ['input', 'prompt', 'question', 'query', 'text']:
                    if key in input_data and isinstance(input_data[key], str):
                        attrs["langchain.input"] = self._truncate_string(
                            input_data[key], self.max_input_length
                        )
                        break
            else:
                attrs["langchain.input_type"] = type(input_data).__name__
        
        return attrs
    
    def _is_langgraph_step(self, args: Tuple, kwargs: Dict[str, Any]) -> bool:
        """Check if this looks like a LangGraph workflow step."""
        # LangGraph steps typically receive a state dict as first argument
        if args and isinstance(args[0], dict):
            state = args[0]
            # Look for common LangGraph state patterns
            return any(key in state for key in [
                'workflow_id', 'state', 'step', 'messages', 'next'
            ])
        return False
    
    def _extract_langgraph_attributes(self, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract LangGraph-specific attributes."""
        attrs = {}
        
        if args and isinstance(args[0], dict):
            state = args[0]
            
            # Extract workflow ID if available
            if 'workflow_id' in state:
                attrs["langchain.workflow_id"] = str(state['workflow_id'])
            
            # Extract step information
            if 'step' in state:
                attrs["langchain.step"] = str(state['step'])
            
            # Count messages if present
            if 'messages' in state and isinstance(state['messages'], list):
                attrs["langchain.messages_count"] = len(state['messages'])
            
            # Extract next steps if available
            if 'next' in state:
                attrs["langchain.next_step"] = str(state['next'])
        
        return attrs
    
    def extract_context(self, args: Tuple, kwargs: Dict[str, Any]) -> Optional[Context]:
        """Extract parent context from LangGraph state."""
        if args and isinstance(args[0], dict):
            state = args[0]
            carrier = state.get('trace_context', {})
            return propagate.extract(carrier)
        return None

    def inject_context(self, result: Any) -> Any:
        """Inject current context into LangGraph state or Command."""
        if not LANGGRAPH_AVAILABLE:
            return result

        new_carrier = {}
        propagate.inject(new_carrier)

        if isinstance(result, Command) and result.update is not None:
            # Command has a mutable 'update' dict
            result.update['trace_context'] = new_carrier
        elif isinstance(result, dict):
            # The result is the update dict itself
            result['trace_context'] = new_carrier

        return result
    
    def _truncate_string(self, value: str, max_length: int) -> str:
        """Truncate string to maximum length."""
        if len(value) > max_length:
            return value[:max_length] + "..."
        return value 