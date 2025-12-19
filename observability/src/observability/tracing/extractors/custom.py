"""
Custom extractor for user-defined operation types.

This extractor provides a flexible way to create custom observability patterns
for specific business operations or domain-specific functionality.
"""

from collections.abc import Callable
from typing import Any

from .base import AttributeExtractor


class CustomExtractor(AttributeExtractor):
    """
    Flexible extractor for custom operation types.

    This extractor allows you to define custom attribute extraction logic
    for domain-specific operations that don't fit into standard categories.

    Example usage:
        @trace(extractor=CustomExtractor(
            operation_type="ml_inference",
            attributes={"model.name": "recommendation_v2"},
            attribute_extractors={
                "input.shape": lambda func, args, kwargs: (
                    str(args[0].shape) if args else None
                ),
                "batch.size": lambda func, args, kwargs: (
                    len(args[0]) if args else None
                ),
            }
        ))
        def predict(features):
            return model.predict(features)
    """

    def __init__(
        self,
        operation_type: str = "custom",
        attributes: dict[str, Any] | None = None,
        attribute_extractors: dict[str, Callable] | None = None,
        span_name_template: str | None = None,
        metrics_labels: dict[str, str | Callable] | None = None,
    ):
        """
        Initialize custom extractor.

        Args:
            operation_type: Type of operation for categorization
            attributes: Static attributes to add to all spans
            attribute_extractors: Functions to extract dynamic attributes
                                 Format:
                                 {attribute_name: function(func, args, kwargs) -> value}
            span_name_template:
            Template for span names (supports {operation_type}, {func_name})
            metrics_labels: Labels for metrics (static values or functions)
        """
        self.operation_type = operation_type
        self.attributes = attributes or {}
        self.attribute_extractors = attribute_extractors or {}
        self.span_name_template = span_name_template or "{operation_type}.{func_name}"
        self.metrics_labels = metrics_labels or {}

    def extract_attributes(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> dict[str, Any]:
        """Extract custom attributes from function call."""
        attrs = {
            "operation.type": self.operation_type,
            "operation.function": func.__name__,
        }

        # Add static attributes
        attrs.update(self.attributes)

        # Add dynamic attributes
        for attr_name, extractor_func in self.attribute_extractors.items():
            try:
                value = extractor_func(func, args, kwargs)
                if value is not None:
                    attrs[attr_name] = value
            except Exception as e:
                # Log error but don't fail the operation
                attrs[f"{attr_name}.error"] = str(e)

        return attrs

    def get_span_name(self, func: Callable, args: tuple, kwargs: dict[str, Any]) -> str:
        """Generate span name using template."""
        return self.span_name_template.format(
            operation_type=self.operation_type, func_name=func.__name__
        )

    def get_metrics_labels(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> dict[str, str]:
        """Generate metrics labels using static and dynamic values."""
        labels = {
            "operation": func.__name__,
            "operation_type": self.operation_type,
        }

        # Add configured labels
        for label_name, label_value in self.metrics_labels.items():
            try:
                if callable(label_value):
                    value = label_value(func, args, kwargs)
                    if value is not None:
                        labels[label_name] = str(value)
                else:
                    labels[label_name] = str(label_value)
            except Exception:
                # Skip labels that fail to extract
                pass

        return labels


class BusinessOperationExtractor(CustomExtractor):
    """
    Specialized extractor for business operations.

    This is a convenience extractor for common business operation patterns.

    Example usage:
        @trace(extractor=BusinessOperationExtractor(
            operation_name="user_registration",
            business_context="authentication",
            include_user_id=True
        ))
        def register_user(user_data):
            return create_user(user_data)
    """

    def __init__(
        self,
        operation_name: str,
        business_context: str | None = None,
        include_user_id: bool = False,
        include_tenant_id: bool = False,
        user_id_extractor: Callable | None = None,
        tenant_id_extractor: Callable | None = None,
        **kwargs: Any,
    ) -> None:
        """
        Initialize business operation extractor.

        Args:
            operation_name: Name of the business operation
            business_context: Business context/domain
            include_user_id: Whether to extract user ID
            include_tenant_id: Whether to extract tenant ID
            user_id_extractor: Function to extract user ID from arguments
            tenant_id_extractor: Function to extract tenant ID from arguments
            **kwargs: Additional arguments passed to CustomExtractor
        """
        attributes = {
            "business.operation": operation_name,
        }

        if business_context:
            attributes["business.context"] = business_context

        attribute_extractors = {}

        if include_user_id:
            if user_id_extractor:
                attribute_extractors["business.user_id"] = user_id_extractor
            else:
                attribute_extractors["business.user_id"] = (
                    self._default_user_id_extractor
                )

        if include_tenant_id:
            if tenant_id_extractor:
                attribute_extractors["business.tenant_id"] = tenant_id_extractor
            else:
                attribute_extractors["business.tenant_id"] = (
                    self._default_tenant_id_extractor
                )

        # Merge with user-provided extractors
        if "attribute_extractors" in kwargs:
            attribute_extractors.update(kwargs["attribute_extractors"])
            del kwargs["attribute_extractors"]

        # Merge with user-provided attributes
        if "attributes" in kwargs:
            attributes.update(kwargs["attributes"])
            del kwargs["attributes"]

        super().__init__(
            operation_type="business_operation",
            attributes=attributes,
            attribute_extractors=attribute_extractors,
            span_name_template=f"business.{operation_name}.{{func_name}}",
            **kwargs,
        )

    def _default_user_id_extractor(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> str | None:
        """Default user ID extractor."""
        # Check kwargs for common user ID field names
        for field in ["user_id", "userId", "user", "uid"]:
            if field in kwargs and kwargs[field]:
                return str(kwargs[field])

        # Check if first argument has user_id attribute
        if args:
            first_arg = args[0]
            if isinstance(first_arg, dict):
                for field in ["user_id", "userId", "user", "uid"]:
                    if field in first_arg and first_arg[field]:
                        return str(first_arg[field])
            elif hasattr(first_arg, "user_id"):
                return str(first_arg.user_id)

        return None

    def _default_tenant_id_extractor(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> str | None:
        """Default tenant ID extractor."""
        # Check kwargs for common tenant ID field names
        for field in ["tenant_id", "tenantId", "tenant", "org_id", "organization_id"]:
            if field in kwargs and kwargs[field]:
                return str(kwargs[field])

        # Check if first argument has tenant_id attribute
        if args:
            first_arg = args[0]
            if isinstance(first_arg, dict):
                for field in [
                    "tenant_id",
                    "tenantId",
                    "tenant",
                    "org_id",
                    "organization_id",
                ]:
                    if field in first_arg and first_arg[field]:
                        return str(first_arg[field])
            elif hasattr(first_arg, "tenant_id"):
                return str(first_arg.tenant_id)

        return None


class MLOperationExtractor(CustomExtractor):
    """
    Specialized extractor for machine learning operations.

    Example usage:
        @trace(extractor=MLOperationExtractor(
            model_name="recommendation_model",
            model_version="v2.1",
            operation_type="inference"
        ))
        def predict_recommendations(user_features):
            return model.predict(user_features)
    """

    def __init__(
        self,
        model_name: str,
        model_version: str | None = None,
        operation_type: str = "inference",
        include_input_shape: bool = True,
        include_batch_size: bool = True,
        **kwargs: Any,
    ) -> None:
        """
        Initialize ML operation extractor.

        Args:
            model_name: Name of the ML model
            model_version: Version of the ML model
            operation_type: Type of ML operation (inference, training, etc.)
            include_input_shape: Whether to extract input tensor shape
            include_batch_size: Whether to extract batch size
            **kwargs: Additional arguments passed to CustomExtractor
        """
        attributes = {
            "ml.model.name": model_name,
            "ml.operation.type": operation_type,
        }

        if model_version:
            attributes["ml.model.version"] = model_version

        attribute_extractors = {}

        if include_input_shape:
            attribute_extractors["ml.input.shape"] = self._extract_input_shape

        if include_batch_size:
            attribute_extractors["ml.batch.size"] = self._extract_batch_size

        # Merge with user-provided extractors and attributes
        if "attribute_extractors" in kwargs:
            attribute_extractors.update(kwargs["attribute_extractors"])
            del kwargs["attribute_extractors"]

        if "attributes" in kwargs:
            attributes.update(kwargs["attributes"])
            del kwargs["attributes"]

        super().__init__(
            operation_type="ml_operation",
            attributes=attributes,
            attribute_extractors=attribute_extractors,
            span_name_template=f"ml.{operation_type}.{model_name}",
            **kwargs,
        )

    def _extract_input_shape(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> str | None:
        """Extract input tensor shape."""
        if args:
            first_arg = args[0]
            if hasattr(first_arg, "shape"):
                return str(first_arg.shape)
        return None

    def _extract_batch_size(
        self, func: Callable, args: tuple, kwargs: dict[str, Any]
    ) -> str | None:
        """Extract batch size from input."""
        if args:
            first_arg = args[0]
            if hasattr(first_arg, "shape") and len(first_arg.shape) > 0:
                return str(first_arg.shape[0])
            elif hasattr(first_arg, "__len__"):
                return str(len(first_arg))
        return None
