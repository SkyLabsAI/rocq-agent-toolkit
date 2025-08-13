# Tracing Guide for Workflow Pipelines

This guide shows you how to add **distributed tracing** to your workflow pipelines using the PSI Verifier observability package.

## What is Tracing?

Tracing creates a "trace tree" of your workflow execution, showing:
- **Spans**: Each operation or step in your workflow
- **Nested spans**: When functions call other functions
- **Timing**: How long each step takes
- **Attributes**: Metadata about each operation
- **Events**: Important moments during execution

## Quick Start

### 1. Enable Tracing in Configuration

```python
from psi_verifier.observability import ObservabilityConfig, setup_observability

obs_config = ObservabilityConfig(
    service_name="my_workflow_service",
    enable_tracing=True,    # Enable tracing!
    enable_logging=True,    # Keep logging enabled
)

setup_observability(obs_config)
```

### 2. Import Tracing Functions

```python
from psi_verifier.observability import (
    trace,              # Main decorator
    get_current_span,   # Get current span
    set_span_attribute, # Add attributes to span
    add_span_event,     # Add events to span
)
```

### 3. Add @trace Decorator to Your Functions

```python
@trace(extractor="workflow", workflow_type="user_verification")
def validate_user_input(user_data):
    # Your existing code here
    return result
```

## Available Extractors

The observability package provides several extractors for different types of operations:

### 1. Workflow Extractor (Best for Pipelines)

```python
@trace(extractor="workflow", workflow_type="data_processing")
def process_data(input_data):
    # Your workflow step
    return processed_data
```

### 2. Database Extractor

```python
@trace(extractor="database", system="postgresql", table="users")
def get_user_from_db(user_id):
    # Database operation
    return user_data
```

### 3. HTTP Extractor

```python
@trace(extractor="http")
def handle_api_request(request):
    # HTTP endpoint
    return response
```

### 4. Custom Extractor

```python
@trace(extractor="custom", 
       operation_type="ml_inference",
       attributes={"model": "v2.1", "stage": "production"})
def run_ml_model(features):
    # Custom operation
    return predictions
```

### 5. RPC Extractor

```python
@trace(extractor="rpc", system="grpc")
def call_remote_service(request):
    # RPC call
    return response
```

## Adding Attributes and Events

### Set Attributes on Current Span

```python
@trace(extractor="workflow", workflow_type="processing")
def process_document(doc):
    # Add custom attributes
    set_span_attribute("document.type", doc.type)
    set_span_attribute("document.size", len(doc.content))
    set_span_attribute("processing.complexity", "high")
    
    # Add events
    add_span_event("Document validation started")
    
    # Your processing logic
    result = process(doc)
    
    add_span_event("Document processing completed", {
        "result_size": len(result),
        "status": "success"
    })
    
    return result
```

### Manual Span Management

```python
def complex_operation(data):
    # Get current span and add attributes
    span = get_current_span()
    if span:
        span.set_attribute("operation.phase", "initialization")
        span.add_event("Starting complex operation")
    
    # Your code here
    return result
```

## Manual Tracing with Context Manager

For more control, use the `trace_context` context manager:

```python
def multi_step_process(input_data):
    with trace_context("multi_step_analysis", 
                       extractor="workflow", 
                       workflow_type="advanced_processing") as span:
        
        # Step 1
        span.set_attribute("step.phase", "initialization")
        span.add_event("Initialization started")
        init_result = initialize(input_data)
        
        # Step 2
        span.set_attribute("step.phase", "processing")
        span.add_event("Processing started")
        processed = process(init_result)
        
        # Step 3
        span.set_attribute("step.phase", "finalization")
        span.add_event("Finalization started")
        final_result = finalize(processed)
        
        # Final attributes
        span.set_attribute("steps.completed", 3)
        span.set_attribute("processing.result", "success")
        
        return final_result
```

## Error Handling with Tracing

Tracing automatically captures exceptions, but you can add custom error information:

```python
@trace(extractor="workflow", workflow_type="error_handling")
def risky_operation(data):
    try:
        # Your risky code
        result = perform_operation(data)
        set_span_attribute("operation.result", "success")
        return result
    except ValueError as e:
        # Add error context
        set_span_attribute("error.type", "validation_error")
        set_span_attribute("error.details", str(e))
        add_span_event("Validation error occurred", {"error": str(e)})
        raise
```

## Nested Tracing (Function Calls)

When traced functions call other traced functions, you get nested spans automatically:

```python
@trace(extractor="workflow", workflow_type="main_pipeline")
def run_pipeline(input_data):
    # This creates the parent span
    validated = validate_input(input_data)      # Child span 1
    processed = process_data(validated)         # Child span 2
    result = generate_output(processed)         # Child span 3
    return result

@trace(extractor="workflow", workflow_type="validation")
def validate_input(data):
    # This creates a child span under run_pipeline
    return validated_data

@trace(extractor="workflow", workflow_type="processing")
def process_data(data):
    # This creates another child span under run_pipeline
    return processed_data
```

## Best Practices

### 1. Use Descriptive Span Names

```python
# Good
@trace(extractor="workflow", workflow_type="user_onboarding")
def validate_user_email(email):
    pass

# Better - the span name will be "workflow.user_onboarding.validate_user_email"
```

### 2. Add Meaningful Attributes

```python
@trace(extractor="workflow", workflow_type="data_processing")
def process_batch(batch_data):
    set_span_attribute("batch.size", len(batch_data))
    set_span_attribute("batch.type", batch_data.type)
    set_span_attribute("processing.strategy", "parallel")
```

### 3. Use Events for Important Milestones

```python
@trace(extractor="workflow", workflow_type="model_training")
def train_model(dataset):
    add_span_event("Training started")
    
    # Training logic
    for epoch in range(10):
        # ... training code ...
        add_span_event(f"Epoch {epoch} completed", {"loss": current_loss})
    
    add_span_event("Training completed")
```

### 4. Be Careful with Sensitive Data

```python
# DON'T include sensitive data in spans
@trace(extractor="workflow", workflow_type="auth", include_args=False)  # Disable argument logging
def authenticate_user(username, password):
    # Only add non-sensitive attributes
    set_span_attribute("auth.username", username)  # OK
    # set_span_attribute("auth.password", password)  # DON'T DO THIS!
    
    return auth_result
```

## Viewing Traces

With your Docker Compose setup, traces will be sent to:
- **Tempo**: For trace storage
- **Grafana**: For trace visualization

You can view your traces in Grafana by:
1. Going to your Grafana dashboard
2. Selecting the "Explore" tab
3. Choosing "Tempo" as the data source
4. Searching for traces by service name or trace ID

## Example: Complete Workflow Pipeline

Here's a complete example of a traced workflow pipeline:

```python
@trace(extractor="workflow", workflow_type="document_processing_pipeline")
def process_document_pipeline(document):
    """Main pipeline with full tracing"""
    logger.info("Starting document processing pipeline")
    
    # Step 1: Validate
    validated_doc = validate_document(document)
    
    # Step 2: Extract
    extracted_data = extract_content(validated_doc)
    
    # Step 3: Process
    processed_data = process_content(extracted_data)
    
    # Step 4: Generate output
    final_result = generate_report(processed_data)
    
    # Add pipeline summary
    set_span_attribute("pipeline.steps_completed", 4)
    set_span_attribute("pipeline.status", "success")
    
    logger.info("Document processing pipeline completed")
    return final_result

@trace(extractor="workflow", workflow_type="validation")
def validate_document(doc):
    set_span_attribute("doc.type", doc.type)
    set_span_attribute("doc.size_bytes", len(doc.content))
    add_span_event("Document validation completed")
    return doc

@trace(extractor="workflow", workflow_type="extraction")
def extract_content(doc):
    # Content extraction logic
    set_span_attribute("extracted.sections", 5)
    return extracted_content

@trace(extractor="workflow", workflow_type="processing")
def process_content(content):
    # Processing logic
    set_span_attribute("processing.algorithm", "nlp_v2")
    return processed_content

@trace(extractor="workflow", workflow_type="generation")
def generate_report(data):
    # Report generation
    set_span_attribute("report.format", "json")
    set_span_attribute("report.size", len(data))
    return report
```

This creates a beautiful trace tree showing the complete pipeline execution with timing, attributes, and relationships between all steps!

## Next Steps

1. **Run the example**: Execute `event_based_custom_logs_with_tracing.py` to see tracing in action
2. **Add tracing to your pipelines**: Start with the `@trace` decorator on your main functions
3. **View traces in Grafana**: Use your existing Docker Compose setup to view traces
4. **Customize extractors**: Create custom extractors for your specific use cases

Your logs will continue to work as before, but now you'll also have distributed tracing showing the complete flow of your workflow pipelines! 