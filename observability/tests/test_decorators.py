"""
Fixed tests for observability.core.decorators module
Focus on functional behavior rather than internal implementation details
"""
import pytest
import asyncio
from unittest.mock import patch, MagicMock
from observability.core.decorators import (
    trace, 
    trace_http, 
    trace_rpc, 
    trace_database, 
    trace_workflow, 
    trace_langchain
)


class TestTraceDecorator:
    """Test the main trace decorator functionality"""

    @patch('observability.core.decorators.otel_trace.get_tracer')
    def test_trace_decorator_basic_functionality(self, mock_get_tracer):
        """Test basic trace decorator functionality"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace(name="test_operation")
        def test_function(x, y):
            return x + y
        
        result = test_function(2, 3)
        
        assert result == 5
        mock_get_tracer.assert_called()
        mock_tracer.start_as_current_span.assert_called()

    @patch('observability.core.decorators.otel_trace.get_tracer')
    @pytest.mark.asyncio
    async def test_trace_decorator_async_function(self, mock_get_tracer):
        """Test trace decorator on asynchronous function"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace(name="async_test_operation")
        async def async_test_function(x, y):
            return x + y
        
        result = await async_test_function(3, 4)
        
        assert result == 7
        mock_get_tracer.assert_called()

    @patch('observability.core.decorators.otel_trace.get_tracer')
    def test_trace_decorator_with_custom_attributes(self, mock_get_tracer):
        """Test trace decorator with custom attributes"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace(name="custom_operation", attributes={"service": "test", "version": "1.0"})
        def custom_function(data):
            return f"processed: {data}"
        
        result = custom_function("test_data")
        
        assert result == "processed: test_data"
        mock_get_tracer.assert_called()
        # Verify span attributes were set (may be called multiple times)
        mock_span.set_attribute.assert_called()

    @patch('observability.core.decorators.otel_trace.get_tracer')
    def test_trace_decorator_handles_exceptions(self, mock_get_tracer):
        """Test trace decorator exception handling"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace(name="failing_operation")
        def failing_function():
            raise ValueError("Test exception")
        
        with pytest.raises(ValueError, match="Test exception"):
            failing_function()
        
        # Verify tracer was called
        mock_get_tracer.assert_called()


class TestSpecializedDecorators:
    """Test specialized trace decorators"""

    def test_trace_http_decorator_exists(self):
        """Test that trace_http decorator exists and is callable"""
        decorator = trace_http(name="http_test")
        assert callable(decorator)

    def test_trace_rpc_decorator_exists(self):
        """Test that trace_rpc decorator exists and is callable"""
        decorator = trace_rpc(name="rpc_test")
        assert callable(decorator)

    def test_trace_database_decorator_exists(self):
        """Test that trace_database decorator exists and is callable"""
        decorator = trace_database(name="db_test")
        assert callable(decorator)

    def test_trace_workflow_decorator_exists(self):
        """Test that trace_workflow decorator exists and is callable"""
        decorator = trace_workflow(name="workflow_test")
        assert callable(decorator)

    def test_trace_langchain_decorator_exists(self):
        """Test that trace_langchain decorator exists and is callable"""
        decorator = trace_langchain(name="llm_test")
        assert callable(decorator)

    @patch('observability.core.decorators.otel_trace.get_tracer')
    def test_specialized_decorators_work(self, mock_get_tracer):
        """Test that specialized decorators actually work"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace_http(name="http_operation")
        def http_request():
            return {"status": "success"}
        
        @trace_database(name="db_operation")
        def db_query():
            return ["result1", "result2"]
        
        @trace_workflow(name="workflow_operation")
        def workflow_step():
            return "workflow_complete"
        
        # Test all decorators work
        http_result = http_request()
        db_result = db_query()
        workflow_result = workflow_step()
        
        assert http_result == {"status": "success"}
        assert db_result == ["result1", "result2"]
        assert workflow_result == "workflow_complete"
        
        # Verify tracer was called for each
        assert mock_get_tracer.call_count >= 3


class TestDecoratorEdgeCases:
    """Test edge cases and error handling"""

    def test_trace_without_name_works(self):
        """Test trace decorator without explicit name"""
        @trace()
        def unnamed_function():
            return "success"
        
        result = unnamed_function()
        assert result == "success"

    def test_trace_with_class_method(self):
        """Test trace decorator on class methods"""
        class TestClass:
            @trace(name="class_method")
            def method(self, value):
                return f"method_result: {value}"
            
            @classmethod
            @trace(name="class_method_static")
            def class_method(cls, value):
                return f"class_result: {value}"
        
        instance = TestClass()
        result1 = instance.method("test")
        result2 = TestClass.class_method("test")
        
        assert result1 == "method_result: test"
        assert result2 == "class_result: test"

    def test_trace_preserves_function_metadata(self):
        """Test that trace decorator preserves function metadata"""
        @trace(name="metadata_test")
        def documented_function(x, y):
            """This function adds two numbers."""
            return x + y
        
        assert documented_function.__name__ == "documented_function"
        assert "adds two numbers" in documented_function.__doc__

    def test_trace_with_various_parameters(self):
        """Test trace decorator with various parameter combinations"""
        @trace(name="param_test", include_args=True, include_result=True)
        def param_function(a, b, c=None):
            return {"a": a, "b": b, "c": c}
        
        result = param_function(1, 2, c=3)
        assert result == {"a": 1, "b": 2, "c": 3}

    @patch('observability.core.decorators.otel_trace.get_tracer')
    @pytest.mark.asyncio 
    async def test_trace_async_with_exception(self, mock_get_tracer):
        """Test trace decorator with async function that raises exception"""
        mock_tracer = MagicMock()
        mock_span = MagicMock()
        mock_tracer.start_as_current_span.return_value.__enter__ = MagicMock(return_value=mock_span)
        mock_tracer.start_as_current_span.return_value.__exit__ = MagicMock(return_value=None)
        mock_get_tracer.return_value = mock_tracer
        
        @trace(name="async_failing")
        async def async_failing_function():
            raise RuntimeError("Async failure")
        
        with pytest.raises(RuntimeError, match="Async failure"):
            await async_failing_function()
        
        mock_get_tracer.assert_called()


class TestDecoratorIntegration:
    """Test decorator integration scenarios"""

    def test_multiple_decorators_on_same_function(self):
        """Test multiple decorators on the same function"""
        @trace_http(name="multi_decorated")
        @trace_database(name="multi_decorated_db")
        def multi_decorated_function():
            return "multi_success"
        
        result = multi_decorated_function()
        assert result == "multi_success"

    def test_decorator_with_complex_function_signature(self):
        """Test decorator with complex function signatures"""
        @trace(name="complex_signature")
        def complex_function(arg1, arg2, *args, kwarg1=None, kwarg2="default", **kwargs):
            return {
                "arg1": arg1,
                "arg2": arg2,
                "args": args,
                "kwarg1": kwarg1,
                "kwarg2": kwarg2,
                "kwargs": kwargs
            }
        
        result = complex_function("a", "b", "c", "d", kwarg1="test", extra="value")
        
        assert result["arg1"] == "a"
        assert result["arg2"] == "b"
        assert result["args"] == ("c", "d")
        assert result["kwarg1"] == "test"
        assert result["kwarg2"] == "default"
        assert result["kwargs"] == {"extra": "value"}

    def test_nested_traced_functions(self):
        """Test nested functions with trace decorators"""
        @trace(name="outer_function")
        def outer_function():
            @trace(name="inner_function")
            def inner_function():
                return "inner_result"
            
            inner_result = inner_function()
            return f"outer_{inner_result}"
        
        result = outer_function()
        assert result == "outer_inner_result"

    def test_decorator_error_resilience(self):
        """Test that decorated functions work even if tracing fails"""
        # This test doesn't mock anything - it tests real resilience
        @trace(name="resilient_function")
        def resilient_function(value):
            return f"processed_{value}"
        
        # Should work even without proper OpenTelemetry setup
        result = resilient_function("test")
        assert result == "processed_test"
