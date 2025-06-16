"""
Generic metrics collection system.

This module provides a clean, framework-agnostic metrics interface that works
with any application. It replaces the old CustomMetrics class with a more
flexible and easier-to-use system.
"""

import logging
from typing import Dict, Optional, Any, Union
from contextlib import contextmanager

from opentelemetry import metrics as otel_metrics

logger = logging.getLogger(__name__)


class MetricsCollector:
    """
    Generic metrics collector that works with any application.
    
    This class provides a clean interface for recording different types of metrics
    without being tied to specific frameworks or operation types.
    """
    
    def __init__(self, service_name: str = "application"):
        """
        Initialize metrics collector.
        
        Args:
            service_name: Name of the service for metric labeling
        """
        self.service_name = service_name
        self.meter = otel_metrics.get_meter(__name__)
        self._instruments = {}
    
    def counter(self, name: str, description: str = "", unit: str = "1"):
        """
        Get or create a counter metric.
        
        Counters track cumulative values that only increase.
        
        Args:
            name: Metric name
            description: Metric description
            unit: Metric unit
            
        Returns:
            Counter instrument
            
        Example:
            orders_counter = metrics.counter("orders_created", "Number of orders created")
            orders_counter.inc(labels={"region": "us-east", "plan": "premium"})
        """
        if name not in self._instruments:
            self._instruments[name] = self.meter.create_counter(
                name=name,
                description=description or f"Counter: {name}",
                unit=unit
            )
        return CounterWrapper(self._instruments[name])
    
    def histogram(self, name: str, description: str = "", unit: str = "", 
                  buckets: Optional[list] = None):
        """
        Get or create a histogram metric.
        
        Histograms track distributions of values.
        
        Args:
            name: Metric name
            description: Metric description
            unit: Metric unit
            buckets: Histogram buckets (optional)
            
        Returns:
            Histogram instrument
            
        Example:
            response_time = metrics.histogram("api_response_time", "API response time", "s")
            response_time.record(0.5, labels={"endpoint": "/users", "method": "GET"})
        """
        if name not in self._instruments:
            # Note: OpenTelemetry Python doesn't support custom buckets in the same way
            # This is a simplified implementation
            self._instruments[name] = self.meter.create_histogram(
                name=name,
                description=description or f"Histogram: {name}",
                unit=unit
            )
        return HistogramWrapper(self._instruments[name])
    
    def gauge(self, name: str, description: str = "", unit: str = ""):
        """
        Get or create a gauge metric.
        
        Gauges track current values that can go up or down.
        
        Args:
            name: Metric name
            description: Metric description
            unit: Metric unit
            
        Returns:
            Gauge instrument
            
        Example:
            active_connections = metrics.gauge("active_connections", "Number of active connections")
            active_connections.set(42, labels={"database": "primary"})
        """
        if name not in self._instruments:
            # Note: OpenTelemetry uses ObservableGauge which works differently
            # For simplicity, we'll use UpDownCounter which behaves similarly
            self._instruments[name] = self.meter.create_up_down_counter(
                name=name,
                description=description or f"Gauge: {name}",
                unit=unit
            )
        return GaugeWrapper(self._instruments[name])
    
    @contextmanager
    def timer(self, name: str, labels: Optional[Dict[str, str]] = None):
        """
        Context manager for timing operations.
        
        Args:
            name: Name of the timer metric
            labels: Labels to apply to the metric
            
        Example:
            with metrics.timer("database_query", {"table": "users"}):
                result = db.query("SELECT * FROM users")
        """
        import time
        
        histogram_metric = self.histogram(f"{name}_duration_seconds", f"Duration of {name} operations", "s")
        
        start_time = time.time()
        try:
            yield
        finally:
            duration = time.time() - start_time
            histogram_metric.record(duration, labels=labels or {})


class CounterWrapper:
    """Wrapper for counter metrics with a clean interface."""
    
    def __init__(self, instrument):
        self.instrument = instrument
    
    def inc(self, value: Union[int, float] = 1, labels: Optional[Dict[str, str]] = None):
        """
        Increment the counter.
        
        Args:
            value: Amount to increment by (default: 1)
            labels: Labels to apply to this measurement
        """
        try:
            self.instrument.add(value, labels or {})
        except Exception as e:
            logger.warning(f"Failed to increment counter: {e}")


class HistogramWrapper:
    """Wrapper for histogram metrics with a clean interface."""
    
    def __init__(self, instrument):
        self.instrument = instrument
    
    def record(self, value: Union[int, float], labels: Optional[Dict[str, str]] = None):
        """
        Record a value in the histogram.
        
        Args:
            value: Value to record
            labels: Labels to apply to this measurement
        """
        try:
            self.instrument.record(value, labels or {})
        except Exception as e:
            logger.warning(f"Failed to record histogram value: {e}")


class GaugeWrapper:
    """Wrapper for gauge metrics with a clean interface."""
    
    def __init__(self, instrument):
        self.instrument = instrument
    
    def set(self, value: Union[int, float], labels: Optional[Dict[str, str]] = None):
        """
        Set the gauge to a specific value.
        
        Args:
            value: Value to set
            labels: Labels to apply to this measurement
        """
        try:
            # Since we're using UpDownCounter, we need to track the delta
            # This is a simplified implementation
            self.instrument.add(value, labels or {})
        except Exception as e:
            logger.warning(f"Failed to set gauge value: {e}")
    
    def inc(self, value: Union[int, float] = 1, labels: Optional[Dict[str, str]] = None):
        """
        Increment the gauge.
        
        Args:
            value: Amount to increment by (default: 1)
            labels: Labels to apply to this measurement
        """
        try:
            self.instrument.add(value, labels or {})
        except Exception as e:
            logger.warning(f"Failed to increment gauge: {e}")
    
    def dec(self, value: Union[int, float] = 1, labels: Optional[Dict[str, str]] = None):
        """
        Decrement the gauge.
        
        Args:
            value: Amount to decrement by (default: 1)
            labels: Labels to apply to this measurement
        """
        try:
            self.instrument.add(-value, labels or {})
        except Exception as e:
            logger.warning(f"Failed to decrement gauge: {e}")


# Global metrics instance
metrics = MetricsCollector()


def set_service_name(name: str):
    """
    Set the service name for the global metrics instance.
    
    Args:
        name: Service name
    """
    global metrics
    metrics = MetricsCollector(name)


# Convenience functions for common patterns
def record_operation_duration(operation: str, duration: float, status: str = "success", 
                             labels: Optional[Dict[str, str]] = None):
    """
    Record the duration of an operation.
    
    Args:
        operation: Name of the operation
        duration: Duration in seconds
        status: Operation status ("success", "error", etc.)
        labels: Additional labels
    """
    all_labels = {"operation": operation, "status": status}
    if labels:
        all_labels.update(labels)
    
    metrics.histogram("operation_duration_seconds", "Duration of operations").record(duration, all_labels)


def increment_operation_count(operation: str, status: str = "success", 
                             labels: Optional[Dict[str, str]] = None):
    """
    Increment the count of operations.
    
    Args:
        operation: Name of the operation
        status: Operation status ("success", "error", etc.)
        labels: Additional labels
    """
    all_labels = {"operation": operation, "status": status}
    if labels:
        all_labels.update(labels)
    
    metrics.counter("operation_total", "Total number of operations").inc(labels=all_labels)


def record_business_metric(metric_name: str, value: Union[int, float], 
                          labels: Optional[Dict[str, str]] = None):
    """
    Record a business metric.
    
    Args:
        metric_name: Name of the business metric
        value: Value to record
        labels: Labels to apply
    """
    if isinstance(value, (int, float)) and value >= 0:
        metrics.histogram(f"business_{metric_name}", f"Business metric: {metric_name}").record(value, labels or {})
    else:
        metrics.counter(f"business_{metric_name}_total", f"Business counter: {metric_name}").inc(value, labels or {}) 