# Observability Examples

- This directory contains examples demonstrating how to use the PSI Verifier observability system for logging and monitoring.
- Use appropiate service_name and log_level for INFORMATIVE LOGGING


## Examples Overview

### 1. Basic Logs (`basic_logs.py`)

The simplest example showing basic logging setup.

**Features:**
- Basic observability configuration
- Standard logging with INFO level
- Simple message logging

### 2. Event-Based Logs (`event_based_logs.py`)

Use event-based logging with structured fields.
There are 4 events:  workflow, training, evaluation, langgraph

```python
logger = get_logger(__name__, event_context="workflow")
```

**Features:**
- Event-based logging with workflow context.
- Structured logging with predefined fields.

### 3. Event-Based Custom Logs (`event_based_custom_logs.py`)

Advanced example with custom log keys.
There are 4 events that can be configured:
- workflow
- training
- evaluation
- langgraph

For any event import either one of the following classes to define extra fields:
- WorkflowEventConfig
- TrainingEventConfig
- EvaluationEventConfig
- LangGraphEventConfig

For each class the following keys are already included:
- TrainingEventConfig
    - hyperparams
    - dataset_info
    - metrics
    - reward_type
    - reward_value


- WorkflowEventConfig:
    - cpp_code
    - gallina_model
    - rep_pred
    - spec
    - node_name
    - raw_llm_response
    - node_count
    - transition_to 
    - status 
    - user_feedback
    - command_execution_result 
    - model_version

- EvaluationEventConfig:
    - dataset_info
    - scores
    - brick_server_result
    - generation_kc
    - sample_predictions: bool = False


- LangGraphEventConfig:
    - graph_state: bool = False
    - node_name
    - transition_to 
    - status 
    - error 


**Features:**
- Extended structured logging with user defined custom fields
- All standard event fields plus custom ones
- One can also pass a dictionary in any of the keys and access those key using (key_dictkey) e.g 
  brick_server_result key has dictionary with key return_code, to access return_code : brick_server_result_return_code

## Running the Examples

To run any of these examples:

```bash
# Basic logging
python -m psi_verifier.observability.examples.basic_logs

# Event-based logging
python -m psi_verifier.observability.examples.event_based_logs

# Event-based custom logging
python -m psi_verifier.observability.examples.event_based_custom_logs
```

## 📊 Dashboard Creation

### Creating Custom Dashboards

Once you have your application logging with the observability package, you can create custom Grafana dashboards to visualize your data:

1. **Sample Dashboard**: Use the provided `sample_dashboard.json` as a starting template
2. **Dashboard Creation Guide**: Follow the comprehensive guide in `dashboard_creation_guide.md`
3. **Import Process**: 
   - Access Grafana (typically `http://localhost:3000`)
   - Go to Dashboards → Import
   - Upload the `sample_dashboard.json` file
   - Customize for your specific use case

### Dashboard Features

The sample dashboard includes:
- **Service Overview**: Total logs, log level distribution, error rates
- **Event Context Analysis**: Distribution of workflow, training, evaluation, and langgraph events
- **Custom Fields**: Analysis of event-specific fields (node_name, status, etc.)
- **Detailed Logs**: Raw log viewing with advanced filtering
- **Dynamic Variables**: Filter by service name, log level, and event context

## Key Concepts

### ObservabilityConfig
The main configuration object that sets up the observability system:
- `service_name`: Identifies your service in logs
- `log_level`: Controls log verbosity (DEBUG, INFO, WARNING, ERROR)

### EventConfig
Extends logging capabilities for event-based applications:
- `extra_fields`: List of additional fields to include in workflow logs
- Enables structured logging for complex workflow states

### Event Context
The `event_context` parameter in `get_logger()` determines the logging context:
- `"workflow"`: Enables workflow-specific structured logging
- Other contexts can be defined based on your application needs

## Best Practices

1. **Start Simple**: Begin with basic logging (`basic_logs.py`) for simple applications
2. **Add Structure**: Use event-based logging for any event applications
3. **Customize Fields**: Define custom fields for domain-specific logging needs
4. **Consistent Naming**: Use consistent service names and field names across your application
5. **Appropriate Log Levels**: Choose log levels that match your monitoring needs

## Integration

These examples show how to integrate the observability system into your PSI Verifier applications. The structured logging approach enables:
- Better log analysis and searching
- Workflow state tracking
- Performance monitoring
- Debugging complex verification processes

### Complete Observability Workflow

1. **Setup Logging**: Use the examples above to integrate logging into your application
2. **Deploy Observability Stack**: Ensure Grafana, Loki, and Prometheus are running
3. **Create Dashboards**: Use the provided sample dashboard and creation guide
4. **Monitor and Iterate**: Customize dashboards based on your specific monitoring needs

## 📁 Files in This Directory

### Logging Examples
- `basic_logs.py` - Simple logging example
- `event_based_logs.py` - Event-based logging with structured fields
- `event_based_custom_logs.py` - Advanced event-based logging with custom fields

### Dashboard Resources
- `sample_dashboard.json` - Template Grafana dashboard for PSI Verifier applications
- `DASHBOARD_QUICKSTART.md` - Quick 5-minute setup guide for dashboards
- `dashboard_creation_guide.md` - Comprehensive guide for creating custom dashboards

### Documentation
- `README.md` - This file, overview of observability examples
