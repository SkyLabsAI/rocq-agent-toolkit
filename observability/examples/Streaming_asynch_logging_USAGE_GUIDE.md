# Auto-Streaming Usage Guide

## Overview

The observability package now supports **automatic streaming log accumulation** with zero code changes to your streaming applications. Just enable auto-streaming in the configuration, and the logger will automatically detect and handle streaming vs non-streaming logs.

## Quick Setup

### 1. Enable Auto-Streaming in Configuration

```python
from observability import ObservabilityConfig, setup_observability, get_logger

# Configure with auto-streaming enabled
config = ObservabilityConfig(
    service_name="your-service-name",
    environment="development",
    
    # 🎯 Enable auto-streaming - this is the key!
    enable_auto_streaming=True,
    
    # 🚀 Enable async logging for non-blocking performance
    enable_async_logging=True,
    async_log_queue_size=1000,
    
    # 🎨 Optionally customize field names (defaults are fine)
    streaming_field_names={
        "user_input": "user_input",
        "accumulated_content": "model_output",  # Use 'model_output' instead of 'accumulated_content'
        "total_chunks": "total_chunks",
        "model": "model",
        "streaming_mode": "streaming_mode",
        "chunk_content": "chunk_content",
        "session_id": "session_id"
    }
)

# Setup once at application startup
setup_observability(config)
```

### 2. Use Regular Logger Everywhere

```python
# Just get a regular logger - no special imports!
logger = get_logger(__name__)
```

## Usage Patterns

### For Streaming Applications

```python
import uuid

# Generate session ID
session_id = str(uuid.uuid4())

# 1. Start streaming session (auto-detected)
logger.info("Starting streaming chat",
           session_id=session_id,
           user_input="Your user's question here",
           model="gpt-4",
           streaming_mode=True)

# 2. Log each chunk as it arrives (automatically accumulated)
for chunk in streaming_response:
    logger.info("Chunk received",
               session_id=session_id,
               chunk_content=chunk)
    yield chunk  # Continue streaming to user

# 3. End session (triggers final aggregated log to Loki)
logger.info("Streaming completed",
           session_id=session_id,
           streaming_complete=True)
```

### For Non-Streaming Applications

```python
# Just log normally - works exactly as before
logger.info("Chat completion finished",
           user_input="User's question",
           model_output="Complete response from model",
           model="gpt-4",
           streaming_mode=False,
           response_time_ms=450)
```

## Automatic Behavior

When auto-streaming is enabled, the logger automatically:

1. **Detects streaming logs** when it sees `session_id` + `chunk_content` or `streaming_mode=True`
2. **Accumulates chunks** in memory for each session
3. **Sends individual chunks** to async queue (debug level) 
4. **Sends final aggregated log** when `streaming_complete=True` is detected
5. **Handles non-streaming logs** normally (no changes needed)

## Final Log Structure

Both streaming and non-streaming logs will have consistent structure:

```json
{
  "timestamp": 1753386431.93,
  "level": "INFO",
  "message": "Streaming session completed",
  "service": "your-service",
  "user_input": "What is machine learning?",
  "model_output": "Machine learning is a subset...",  // or "accumulated_content" 
  "total_chunks": 10,
  "model": "gpt-4",
  "streaming_mode": true,
  "duration_ms": 1002.79,
  "event_type": "streaming_complete"
}
```

## Modifying Your Existing Code

### Minimal Changes Required

1. **Add to your app setup:**
   ```python
   config.enable_auto_streaming = True
   config.enable_async_logging = True
   ```

2. **In your streaming endpoint:**
   ```python
   session_id = str(uuid.uuid4())  # Generate once per request
   
   # Add this line at start
   logger.info("Streaming started", session_id=session_id, user_input=user_input, model=model, streaming_mode=True)
   
   # Add this line for each chunk  
   logger.info("Chunk", session_id=session_id, chunk_content=chunk)
   
   # Add this line at end
   logger.info("Streaming done", session_id=session_id, streaming_complete=True)
   ```

3. **In your non-streaming endpoint:**
   ```python
   # Just add streaming_mode=False to existing logs
   logger.info("Response complete", user_input=input, model_output=response, model=model, streaming_mode=False)
   ```

## Field Name Customization

You can customize field names in the configuration:

```python
streaming_field_names={
    "user_input": "prompt",              # Use "prompt" instead of "user_input"
    "accumulated_content": "response",    # Use "response" instead of "accumulated_content"
    "total_chunks": "chunk_count",       # Use "chunk_count" instead of "total_chunks"
    "model": "llm_model",                # Use "llm_model" instead of "model"
    "streaming_mode": "is_streaming",    # Use "is_streaming" instead of "streaming_mode"
    "chunk_content": "chunk_text",       # Use "chunk_text" instead of "chunk_content"
    "session_id": "request_id"           # Use "request_id" instead of "session_id"
}
```

## Benefits

✅ **Zero imports** - just use regular `get_logger()`  
✅ **Auto-detection** - no manual session management  
✅ **Async processing** - non-blocking streaming performance  
✅ **Configurable** - customize field names as needed  
✅ **Backwards compatible** - existing logs work unchanged  
✅ **Consistent structure** - same format for streaming and non-streaming  

## Cleanup

Remember to cleanup on application shutdown:

```python
from observability import cleanup_async_logging

# Call this in your shutdown handler
cleanup_async_logging()
``` 