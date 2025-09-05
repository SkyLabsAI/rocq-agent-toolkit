"""
RPC call extractor for gRPC and other RPC systems.

This extractor understands RPC calls and extracts standard RPC attributes for tracing.
It supports gRPC and can be extended for other RPC systems.
"""

from typing import Any, Dict, Callable, Tuple, Optional
from .base import AttributeExtractor


class RpcExtractor(AttributeExtractor):
    """
    Extractor for RPC calls (gRPC, internal service calls, etc.).
    
    Supports:
    - gRPC service methods (self, request, context pattern)
    - Internal service calls
    - Any RPC-style function calls
    
    Example usage:
        @trace(extractor="rpc")
        def CreateUser(self, request, context):
            return user_pb2.UserResponse(user_id="123")
            
        @trace(extractor=RpcExtractor(system="internal", service_name="UserService"))
        def get_user_profile(user_id):
            return internal_service.get_profile(user_id)
    """
    
    def __init__(self, 
                 system: str = "grpc",
                 service_name: Optional[str] = None,
                 include_request_data: bool = False,
                 include_response_data: bool = False,
                 max_data_length: int = 1000):
        """
        Initialize RPC extractor.
        
        Args:
            system: RPC system type ("grpc", "internal", "jsonrpc", etc.)
            service_name: Override service name (auto-detected from class name if not provided)
            include_request_data: Whether to include request data in spans
            include_response_data: Whether to include response data in spans
            max_data_length: Maximum length for data attributes
        """
        self.system = system
        self.service_name = service_name
        self.include_request_data = include_request_data
        self.include_response_data = include_response_data
        self.max_data_length = max_data_length
    
    def extract_attributes(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract RPC attributes from function call."""
        attrs = {
            "rpc.system": self.system,
            "rpc.method": func.__name__,
        }
        
        # Determine service name
        service_name = self.service_name
        if not service_name and args and hasattr(args[0], '__class__'):
            service_name = args[0].__class__.__name__
            # Clean up common suffixes
            for suffix in ['Servicer', 'Service', 'Impl']:
                if service_name.endswith(suffix):
                    service_name = service_name[:-len(suffix)]
                    break
        
        if service_name:
            attrs["rpc.service"] = service_name
        
        # gRPC specific attributes
        if self.system == "grpc":
            attrs.update(self._extract_grpc_attributes(func, args, kwargs))
        
        # Include request data if requested
        if self.include_request_data:
            request_data = self._extract_request_data(args, kwargs)
            if request_data:
                attrs.update(request_data)
        
        return attrs
    
    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Generate span name for RPC call."""
        service_name = self.service_name
        if not service_name and args and hasattr(args[0], '__class__'):
            service_name = args[0].__class__.__name__
            # Clean up common suffixes
            for suffix in ['Servicer', 'Service', 'Impl']:
                if service_name.endswith(suffix):
                    service_name = service_name[:-len(suffix)]
                    break
        
        if service_name:
            return f"{service_name}/{func.__name__}"
        else:
            return f"RPC {func.__name__}"
    
    def get_metrics_labels(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, str]:
        """Generate metrics labels for RPC operations."""
        labels = {
            "operation": func.__name__,
            "rpc_system": self.system,
        }
        
        # Add service name if available
        service_name = self.service_name
        if not service_name and args and hasattr(args[0], '__class__'):
            service_name = args[0].__class__.__name__
            for suffix in ['Servicer', 'Service', 'Impl']:
                if service_name.endswith(suffix):
                    service_name = service_name[:-len(suffix)]
                    break
        
        if service_name:
            labels["service"] = service_name
        
        return labels
    
    def extract_error_attributes(self, func: Callable, args: Tuple, kwargs: Dict[str, Any], 
                               exception: Exception) -> Dict[str, Any]:
        """Extract RPC-specific error attributes."""
        attrs = super().extract_error_attributes(func, args, kwargs, exception)
        
        # gRPC specific error handling
        if self.system == "grpc":
            # Try to extract gRPC status code if available
            if hasattr(exception, 'code'):
                attrs["rpc.grpc.status_code"] = str(exception.code())
            
            # Add context information if available (context is usually args[2])
            if len(args) > 2:
                context = args[2]
                if hasattr(context, 'code') and hasattr(context, 'details'):
                    try:
                        # This might be a gRPC context that was set with error details
                        pass  # Additional context extraction could go here
                    except Exception:
                        pass
        
        return attrs
    
    def _extract_grpc_attributes(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract gRPC-specific attributes."""
        attrs = {}
        
        # gRPC methods typically have signature: (self, request, context)
        if len(args) >= 3:
            context = args[2]
            
            # Extract peer information
            if hasattr(context, 'peer'):
                try:
                    peer = context.peer()
                    if peer:
                        attrs["rpc.grpc.peer"] = peer
                except Exception:
                    pass
            
            # Extract metadata
            if hasattr(context, 'invocation_metadata'):
                try:
                    metadata = context.invocation_metadata()
                    if metadata:
                        # Add selected metadata (avoid sensitive info)
                        for key, value in metadata:
                            if not key.startswith('grpc-') and not key.lower().startswith('auth'):
                                attr_key = f"rpc.grpc.metadata.{key}"
                                attrs[attr_key] = self._truncate_string(value)
                except Exception:
                    pass
        
        return attrs
    
    def _extract_request_data(self, args: Tuple, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Extract request data for inclusion in spans."""
        attrs = {}
        
        # For gRPC-style calls, request is typically args[1]
        if len(args) > 1:
            request = args[1]
            attrs["rpc.request.type"] = type(request).__name__
            
            # Try to extract some basic info without being too invasive
            if hasattr(request, 'DESCRIPTOR'):
                # This is likely a protobuf message
                attrs["rpc.request.proto_type"] = request.DESCRIPTOR.full_name
            
            # Add size if we can calculate it
            try:
                if hasattr(request, 'ByteSize'):
                    attrs["rpc.request.size_bytes"] = request.ByteSize()
                elif hasattr(request, '__sizeof__'):
                    attrs["rpc.request.size_bytes"] = request.__sizeof__()
            except Exception:
                pass
        
        return attrs
    
    def _truncate_string(self, value: str) -> str:
        """Truncate string to maximum length."""
        if len(value) > self.max_data_length:
            return value[:self.max_data_length] + "..."
        return value 