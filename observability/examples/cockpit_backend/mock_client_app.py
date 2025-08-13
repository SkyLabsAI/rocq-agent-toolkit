"""
Simple FastAPI Proxy for OpenRouter API.

This is a simple FastAPI server that forwards OpenAI-compatible requests to OpenRouter.
You can send requests with streaming on or off as you wish.

Usage:
    1. Make sure your .env file has OPENROUTER_API_KEY set
    2. Start: uvicorn psi_verifier.cockpit_backend.mock_client_app:app --port 8001
    3. Send requests to: http://localhost:8001/v1/chat/completions
"""

import time
import json
import asyncio
import uuid
import os
import dotenv
from pathlib import Path
from typing import Dict, Any, Optional, AsyncGenerator
import httpx

from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import ValidationError



from psi_verifier.observability import (
    ObservabilityConfig,
    setup_observability,
    get_logger,
)
observability_config = ObservabilityConfig(
    service_name="cockpit_backend_with_auto_streaming_testing",
    environment="development",
    log_level="INFO",
    # 🎯 Enable auto-streaming - this is the key change!
    enable_auto_streaming=True,
    enable_async_logging=True,
    async_log_queue_size=1000,
    
    # 🚀 Generic streaming configuration - works with ANY field names!
    auto_detect_chunk_fields=True,  # Automatically detect any field as chunk content
    accumulated_content_field_name="model_output",  # Final output field name (you can change this!)
    enable_individual_chunk_logging=False,  # Set to True if you want to see individual chunks
)

setup_observability(observability_config)
logger = get_logger(__name__, event_context="cockpit_backend")




try:
    from psi_verifier.cockpit_backend.models import (
        ChatCompletionRequest,
        ChatCompletion,
        ChatCompletionChoice,
        ChatMessage,
        UsageInfo,
    )
except ImportError:
    from models import (
        ChatCompletionRequest,
        ChatCompletion,
        ChatCompletionChoice,
        ChatMessage,
        UsageInfo,
    )

# Load environment variables from .env file in the root directory
env_path = Path(__file__).parent.parent.parent / ".env"
dotenv.load_dotenv(dotenv_path=env_path)

app = FastAPI(title="Simple OpenRouter Proxy", version="1.0.0")

# Configuration from .env file
OPENROUTER_BASE_URL = os.getenv("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1")
OPENROUTER_API_KEY = os.getenv("OPENROUTER_API_KEY", "")
DEFAULT_MODEL = os.getenv("DEFAULT_MODEL", "gpt-3.5-turbo")

# HTTP client for making requests
client = httpx.AsyncClient(timeout=300.0)



async def forward_to_openrouter(request_data: Dict[str, Any]) -> Dict[str, Any]:
    """
    Forward request to OpenRouter API endpoint.
    
    Args:
        request_data: The OpenAI-compatible request data
        
    Returns:
        Response from OpenRouter API
        
    Raises:
        HTTPException: If the OpenRouter request fails
    """
    try:
        if not OPENROUTER_API_KEY:
            raise HTTPException(
                status_code=401,
                detail="OpenRouter API key not configured. Please set OPENROUTER_API_KEY environment variable. "
                       "Get your API key from https://openrouter.ai/"
            )
        
        openrouter_url = f"{OPENROUTER_BASE_URL}/chat/completions"
        
        # Prepare headers
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {OPENROUTER_API_KEY}",
            "HTTP-Referer": "http://localhost:8001",  # Required by OpenRouter
            "X-Title": "PSI Verifier Mock Client"
        }
        
        # Simple log of user input
        user_message = request_data.get("messages", [])[-1].get("content", "") if request_data.get("messages") else ""
        logger.info("NON-STREAMING Request", 
                   user_input=user_message,
                   model=request_data.get("model"),
                   streaming_mode=False)
        
        response = await client.post(
            openrouter_url,
            json=request_data,
            headers=headers
        )
        
        if response.status_code != 200:
            raise HTTPException(
                status_code=response.status_code,
                detail=f"OpenRouter API error: {response.text}"
            )
        
        response_data = response.json()
        
        # Simple log of model output
        response_content = ""
        if response_data.get("choices") and len(response_data["choices"]) > 0:
            response_content = response_data["choices"][0].get("message", {}).get("content", "")
        
        # Simple log of user input
        user_message = request_data.get("messages", [])[-1].get("content", "") if request_data.get("messages") else ""
        
        logger.info("NON-STREAMING Response", 
                   user_input=user_message,
                   model_output=response_content,
                   model=request_data.get("model"),
                   streaming_mode=False)
        
        return response_data
        
    except httpx.RequestError as e:
        raise HTTPException(
            status_code=503,
            detail=f"Failed to connect to OpenRouter API: {str(e)}"
        )



async def forward_streaming_to_openrouter(request_data: Dict[str, Any]) -> AsyncGenerator[str, None]:
    # Generate session ID for auto-streaming accumulation
    session_id = str(uuid.uuid4())
    chunk_counter = 0
    
    try:
        if not OPENROUTER_API_KEY:
            raise HTTPException(
                status_code=401,
                detail="OpenRouter API key not configured"
            )
        
        openrouter_url = f"{OPENROUTER_BASE_URL}/chat/completions"
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {OPENROUTER_API_KEY}",
            "HTTP-Referer": "http://localhost:8001",
            "X-Title": "PSI Verifier Mock Client",
            "Accept": "text/event-stream",
        }
        
        user_message = request_data.get("messages", [])[-1].get("content", "") if request_data.get("messages") else ""
        logger.info("STREAMING Request", 
                   session_id=session_id,
                   user_input=user_message,
                   model=request_data.get("model"),
                   streaming_mode=True)
        
        async with client.stream(
            "POST",
            openrouter_url,
            json=request_data,
            headers=headers
        ) as response:
            logger.info("STREAMING Response Status", 
                       status_code=response.status_code,
                       headers=dict(response.headers))
            if response.status_code != 200:
                error_text = await response.aread()
                raise HTTPException(
                    status_code=response.status_code,
                    detail=f"OpenRouter streaming API error: {error_text.decode()}"
                )
            
            async for chunk in response.aiter_text():
                if chunk.strip():
                    logger.debug("RAW CHUNK", raw_chunk=chunk)  # Log raw chunk for debugging
                    for line in chunk.strip().split('\n'):
                        if line.startswith('data: '):
                            data = line[6:].strip()  # Remove extra whitespace
                            
                            # Skip empty data lines or completion markers
                            if not data or data == '[DONE]':
                                continue
                                
                            logger.debug("RAW SSE DATA", raw_data=data)
                            
                            try:
                                chunk_data = json.loads(data)
                                logger.debug("PARSED CHUNK DATA", chunk_data=chunk_data)
                                
                                # Validate chunk structure before processing
                                if (isinstance(chunk_data, dict) and 
                                    'choices' in chunk_data and 
                                    len(chunk_data['choices']) > 0):
                                    
                                    delta = chunk_data['choices'][0].get('delta', {})
                                    content = delta.get('content')
                                    
                                    if content:
                                        chunk_counter += 1
                                        # Let the auto-streaming logger accumulate content automatically
                                        logger.info("STREAMING Chunk", 
                                                   session_id=session_id,
                                                   content=content,  # You can use ANY field name now!
                                                   chunk_number=chunk_counter,
                                                   chunk_length=len(content),
                                                   model=request_data.get("model"),
                                                   streaming_mode=True)
                                else:
                                    # Valid JSON but not expected chunk format - log at debug level
                                    logger.debug("Unexpected chunk format", chunk_data=chunk_data)
                                    
                            except json.JSONDecodeError as e:
                                # Only log as warning for non-empty data that fails to parse
                                if data.strip():
                                    logger.warning("Invalid JSON in SSE stream", 
                                                 error=str(e), 
                                                 raw_data=data[:100])  # Limit data length in log
                            except (KeyError, IndexError, TypeError) as e:
                                # Log data structure issues at debug level
                                logger.debug("Chunk structure error", 
                                           error=str(e), 
                                           raw_data=data[:100])
                                yield chunk
    except httpx.RequestError as e:
        logger.error("Streaming request error", error=str(e))
        raise HTTPException(
            status_code=503,
            detail=f"Failed to connect to OpenRouter streaming API: {str(e)}"
        )
    finally:
        # Signal completion to auto-streaming logger (triggers final aggregated log)
        logger.info("STREAMING Complete", 
                   session_id=session_id,
                   streaming_complete=True)

@app.post("/v1/chat/completions")
async def chat_completions(request: Request):
    """
    Forward OpenAI-compatible requests to OpenRouter.
    Supports both streaming and non-streaming modes.
    """
    try:
        # Parse and validate request
        request_data = await request.json()
        chat_request = ChatCompletionRequest.model_validate(request_data)
        
    except json.JSONDecodeError:
        raise HTTPException(status_code=400, detail="Invalid JSON")
    except ValidationError as e:
        raise HTTPException(status_code=422, detail=json.loads(e.json()))

    # Set default model if not specified
    if not request_data.get("model"):
        request_data["model"] = DEFAULT_MODEL
    
    is_streaming = request_data.get("stream", False)
    
    if is_streaming:
        # Streaming response
        return StreamingResponse(
            forward_streaming_to_openrouter(request_data),
            media_type="text/event-stream"
        )
    else:
        # Non-streaming response
        return await forward_to_openrouter(request_data)

@app.get("/")
async def root():
    """Simple status endpoint."""
    return {
        "message": "OpenRouter Proxy Running",
        "openrouter_configured": bool(OPENROUTER_API_KEY),
        "default_model": DEFAULT_MODEL
    }

@app.on_event("shutdown")
async def shutdown_event():
    """Clean up resources on shutdown."""
    await client.aclose()

async def chat_with_model():
    """
    Simple chat interface to test the OpenRouter proxy.
    Send requests and see responses directly.
    """
    print("\n💬 Chat Interface - Testing OpenRouter Proxy")
    print("=" * 50)
    print(f"🤖 Model: {DEFAULT_MODEL}")
    print(f"🔑 API Key configured: {bool(OPENROUTER_API_KEY)}")
    print("💡 Type 'quit' to exit, 'stream' to toggle streaming mode")
    print()
    
    streaming_mode = False
    server_url = "http://localhost:8001"
    
    # Simple log of chat session start
    logger.info("Chat session started", 
               model=DEFAULT_MODEL,
               streaming_mode=streaming_mode)
    
    while True:
        print(f"🎛️  Streaming: {'ON' if streaming_mode else 'OFF'}")
        user_input = input("You: ").strip()
        
        if user_input.lower() in ['quit', 'exit', 'q']:
            logger.info("Chat session ended")
            print("👋 Goodbye!")
            break
        elif user_input.lower() == 'stream':
            streaming_mode = not streaming_mode
            logger.info("Streaming mode toggled", 
                       streaming_mode=streaming_mode)
            print(f"🔄 Streaming mode: {'ON' if streaming_mode else 'OFF'}")
            continue
        elif not user_input:
            continue
        
        # Prepare request
        request_data = {
            "model": DEFAULT_MODEL,
            "messages": [
                {"role": "user", "content": user_input}
            ],
            "stream": streaming_mode,
            "max_tokens": 150,
            "temperature": 0.7
        }
        
        try:
            async with httpx.AsyncClient(timeout=60.0) as client:
                if streaming_mode:
                    # Streaming response
                    print("🤖 Bot: ", end="", flush=True)
                    accumulated_response = ""
                    start_time = time.time()
                    
                    async with client.stream(
                        "POST", 
                        f"{server_url}/v1/chat/completions",
                        json=request_data
                    ) as response:
                        if response.status_code == 200:
                            async for chunk in response.aiter_text():
                                if chunk.strip():
                                    for line in chunk.strip().split('\n'):
                                        if line.startswith('data: '):
                                            data = line[6:]
                                            if data != '[DONE]':
                                                try:
                                                    chunk_data = json.loads(data)
                                                    if 'choices' in chunk_data:
                                                        delta = chunk_data['choices'][0].get('delta', {})
                                                        content = delta.get('content')
                                                        if content:
                                                            print(content, end='', flush=True)
                                                            # accumulated_response += content
                                                            # Log each individual chunk in chat mode
                                                            # logger.info("Chat STREAMING Chunk", 
                                                            #            chunk_content=content,
                                                            #            chunk_length=len(content),
                                                            #            user_input=user_input,
                                                            #            streaming_mode=True)
                                                except json.JSONDecodeError:
                                                    continue
                            print()  # New line after streaming
                            
                            # Simple log of chat response 
                            # logger.info("Chat streaming response", 
                            #            user_input=user_input,
                            #            model_output=accumulated_response,
                            #            streaming_mode=True)
                        else:
                            error_text = await response.aread()
                            error_msg = f"Error: {response.status_code} - {error_text.decode()}"
                            print(f"❌ {error_msg}")
                            logger.error("Chat streaming error", 
                                        user_input=user_input,
                                        error=error_msg,
                                        streaming_mode=True)
                else:
                    # Non-streaming response
                    start_time = time.time()
                    response = await client.post(
                        f"{server_url}/v1/chat/completions",
                        json=request_data
                    )
                    duration_ms = (time.time() - start_time) * 1000
                    
                    if response.status_code == 200:
                        result = response.json()
                        content = result["choices"][0]["message"]["content"]
                        print(f"🤖 Bot: {content}")
                        
                        # Simple log of chat response
                        logger.info("Chat non-streaming response", 
                                   user_input=user_input,
                                   model_output=content,
                                   streaming_mode=False)
                    else:
                        error_msg = f"Error: {response.status_code} - {response.text}"
                        print(f"❌ {error_msg}")
                        logger.error("Chat non-streaming error", 
                                    user_input=user_input,
                                    error=error_msg,
                                    streaming_mode=False)
                        
        except Exception as e:
            error_msg = f"Connection Error: {e}"
            print(f"❌ {error_msg}")
            print("💡 Make sure the server is running!")
            logger.error("Chat connection error", 
                        user_input=user_input,
                        error=error_msg,
                        streaming_mode=streaming_mode)
        
        print()  # Extra line for readability

def start_server():
    """Start the FastAPI server."""
    import uvicorn
    print("🚀 Starting OpenRouter Proxy Server")
    print(f"📡 OpenRouter API configured: {bool(OPENROUTER_API_KEY)}")
    print(f"🤖 Default model: {DEFAULT_MODEL}")
    print("🌐 Server will run at: http://localhost:8001")
    uvicorn.run(app, host="127.0.0.1", port=8001)

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--chat":
        # Chat mode - connect to running server
        asyncio.run(chat_with_model())
    else:
        # Default - start server
        start_server()