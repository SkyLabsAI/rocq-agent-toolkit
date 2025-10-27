import json
import time

from observability import (
    ObservabilityConfig,
    WorkflowEventConfig,
    add_span_event,
    get_current_span,
    get_logger,
    set_span_attribute,
    setup_observability,
    trace,
    trace_context,
)

# --- Observability Setup ---
# A single configuration object now manages both logging and tracing.
workflow_cfg = WorkflowEventConfig(
    extra_fields=[
        "specification_goals",
        "structured_nl_spec",
        "max_user_attempts",
    ]
)

config = ObservabilityConfig(
    service_name="event_based_custom_logs_with_tracing",
    workflow_event_config=workflow_cfg,
    log_level="INFO",
    otlp_endpoint="http://172.31.0.1:4317",
    enable_otlp_log_export=True,
    enable_tracing=True,
)
setup_observability(config)

logger = get_logger(__name__, event_context="workflow")


# =============================================================================
# WORKFLOW PIPELINE EXAMPLES WITH TRACING
# =============================================================================


# Example 1: Basic workflow step with @trace decorator
@trace(extractor="workflow", workflow_type="user_verification")
def validate_user_input(user_data):
    """
    Validate user input - this will be traced as a workflow step
    """
    logger.info(
        "Validating user input",
        spec="validation",
        node_name="validate_input",
        node_count=1,
        transition_to="process_spec",
        specification_goals="validate user data",
        structured_nl_spec="check user input format",
        max_user_attempts=3,
    )
    time.sleep(0.1)
    set_span_attribute("user.id", user_data.get("user_id", "unknown"))
    set_span_attribute("validation.rules_count", 5)
    add_span_event("Validation completed", {"status": "success"})
    return {"valid": True, "processed_fields": 3}


# Example 2: Specification processing with custom attributes
@trace(
    extractor="workflow", workflow_type="specification_processing", include_args=True
)
def process_specification(spec_data, max_attempts=3):
    """
    Process specification - traced with input arguments
    """
    logger.info(
        "Processing specification",
        spec="processing",
        node_name="process_spec",
        node_count=2,
        transition_to="generate_code",
        specification_goals="process user specification",
        structured_nl_spec="analyze and structure specification",
        max_user_attempts=max_attempts,
    )
    time.sleep(0.2)
    current_span = get_current_span()
    if current_span:
        current_span.set_attribute("spec.complexity", "medium")
        current_span.set_attribute(
            "spec.lines_count", len(spec_data.get("content", "").split("\n"))
        )
        current_span.add_event("Specification parsed")
    return {"processed": True, "complexity_score": 0.7}


# Example 3: Code generation with custom extractor
@trace(
    extractor="custom",
    operation_type="code_generation",
    attributes={"component": "gallina_generator", "version": "v2.1"},
)
def generate_gallina_code(processed_spec):
    """
    Generate Gallina code - traced with custom extractor
    """
    logger.info(
        "Generating Gallina code",
        spec="generation",
        node_name="generate_code",
        node_count=3,
        transition_to="verify_code",
        specification_goals="generate formal verification code",
        structured_nl_spec="create Gallina proof code",
        max_user_attempts=1,
    )
    time.sleep(0.3)
    set_span_attribute("code.language", "gallina")
    set_span_attribute("code.lines_generated", 150)
    return {"code": "Gallina code here...", "status": "generated"}


# Example 4: Verification step with database extractor
@trace(extractor="database", system="coq", table="proofs")
def verify_proof(gallina_code):
    """
    Verify proof - traced as database operation
    """
    logger.info(
        "Verifying proof",
        spec="verification",
        node_name="verify_proof",
        node_count=4,
        transition_to="finalize",
        specification_goals="verify generated proof",
        structured_nl_spec="run formal verification",
        max_user_attempts=1,
    )
    time.sleep(0.4)
    set_span_attribute("verification.result", "success")
    set_span_attribute("verification.time_ms", 400)
    return {"verified": True, "proof_valid": True}


# Example 5: Manual tracing with context manager
def complex_pipeline_step(input_data):
    """
    Complex step using manual tracing with context manager
    """
    with trace_context(
        "complex_analysis", extractor="workflow", workflow_type="advanced_processing"
    ) as span:
        logger.info(
            "Starting complex analysis",
            spec="complex",
            node_name="complex_analysis",
            node_count=1,
            transition_to="complete",
            specification_goals="perform complex analysis",
            structured_nl_spec="multi-step analysis process",
            max_user_attempts=1,
        )
        span.set_attribute("step.phase", "initialization")
        span.add_event("Initialization started")
        time.sleep(0.1)
        span.set_attribute("step.phase", "processing")
        span.add_event("Processing started")
        time.sleep(0.2)
        span.set_attribute("step.phase", "finalization")
        span.add_event("Finalization started")
        time.sleep(0.1)
        span.set_attribute("analysis.complexity", "high")
        span.set_attribute("analysis.result", "success")
        return {"analysis_complete": True}


# Example 6: Complete workflow pipeline with nested tracing
@trace(extractor="workflow", workflow_type="complete_pipeline")
def run_complete_pipeline(user_input):
    """
    Complete pipeline that calls other traced functions
    """
    logger.info(
        "Starting complete pipeline",
        spec="pipeline",
        node_name="pipeline_start",
        node_count=1,
        transition_to="validate",
        specification_goals="complete user verification pipeline",
        structured_nl_spec="end-to-end processing pipeline",
        max_user_attempts=1,
    )
    validated_data = validate_user_input(user_input)
    processed_spec = process_specification(validated_data)
    generated_code = generate_gallina_code(processed_spec)
    verification_result = verify_proof(generated_code)
    complex_result = complex_pipeline_step(verification_result)
    set_span_attribute("pipeline.steps_completed", 5)
    set_span_attribute("pipeline.status", "success")
    logger.info(
        "Pipeline completed successfully",
        spec="pipeline",
        node_name="pipeline_complete",
        node_count=5,
        transition_to="end",
        specification_goals="pipeline execution complete",
        structured_nl_spec="all steps completed successfully",
        max_user_attempts=1,
    )
    return {
        "pipeline_complete": True,
        "validation": validated_data,
        "processing": processed_spec,
        "generation": generated_code,
        "verification": verification_result,
        "complex_analysis": complex_result,
    }


# Example 7: Error handling with tracing
@trace(extractor="workflow", workflow_type="error_handling")
def error_prone_step(data):
    """
    Example of error handling with tracing
    """
    logger.info(
        "Starting error-prone step",
        spec="error_handling",
        node_name="error_step",
        node_count=1,
        transition_to="error_or_success",
        specification_goals="demonstrate error handling",
        structured_nl_spec="step that might fail",
        max_user_attempts=3,
    )
    if data.get("cause_error", False):
        set_span_attribute("error.type", "simulated_error")
        logger.error(
            "Simulated error occurred",
            spec="error_handling",
            node_name="error_step",
            error_type="simulated_error",
        )
        raise ValueError("Simulated error for demonstration")
    set_span_attribute("step.result", "success")
    return {"status": "success"}


# =============================================================================
# MAIN EXECUTION
# =============================================================================

if __name__ == "__main__":
    logger.info("Starting traced workflow pipeline example")
    user_input = {
        "user_id": "user123",
        "content": """This is a test specification\nwith multiple lines\nfor
        demonstration""",
        "max_attempts": 3,
    }
    try:
        result = run_complete_pipeline(user_input)
        logger.info(
            "Pipeline execution completed",
            spec="completion",
            node_name="main_complete",
            node_count=1,
            transition_to="end",
            specification_goals="demonstrate tracing capabilities",
            structured_nl_spec="complete example execution",
            max_user_attempts=1,
        )
        print("Pipeline Result:", json.dumps(result, indent=2))
    except Exception as e:
        logger.error(
            "Pipeline failed",
            spec="error",
            node_name="main_error",
            error_type=type(e).__name__,
            error_message=str(e),
        )
        raise
    try:
        error_data = {"cause_error": True}
        error_prone_step(error_data)
    except ValueError:
        logger.info(
            "Error handled successfully",
            spec="error_handling",
            node_name="error_handled",
            error_type="ValueError",
        )
    logger.info("All examples completed successfully")
