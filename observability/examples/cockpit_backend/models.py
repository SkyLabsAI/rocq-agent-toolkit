"""
Data models for the OpenAI-compatible API server.

This module defines the Pydantic models used to represent requests and responses
in the OpenAI Chat Completions API format. These models enforce validation and
provide typing for both streaming and non-streaming responses.
"""

from typing import List, Optional, Dict, Union, Literal, Any
from pydantic import BaseModel

# Common Structures

class ChatMessage(BaseModel):
    """
    Represents a message in a chat conversation.
    
    Chat messages are the fundamental units of conversation in the Chat Completions API,
    with each message having a role (system, user, assistant, or tool) and content.
    
    Attributes:
        role: The role of the message sender - "system", "user", "assistant", or "tool".
        content: The content of the message. Can be None for certain message types.
        tool_calls: Tool calls requested by the assistant.
        tool_call_id: ID of the tool call being responded to.
    """
    role: Literal["system", "user", "assistant", "tool"]
    content: Optional[str] = None
    # Tool calls related fields (optional)
    tool_calls: Optional[List[Dict[str, Any]]] = None # Placeholder for tool call structure
    tool_call_id: Optional[str] = None


class UsageInfo(BaseModel):
    """
    Represents token usage information.
    
    Contains statistics about token consumption for both the prompt and completion parts
    of a request, useful for tracking API usage.
    
    Attributes:
        prompt_tokens: Number of tokens used in the prompt.
        completion_tokens: Number of tokens used in the completion.
        total_tokens: Total number of tokens used (prompt + completion).
    """
    prompt_tokens: int
    completion_tokens: Optional[int] = None
    total_tokens: int


# Non-Streaming Structures

class ChatCompletionChoice(BaseModel):
    """
    Represents a single completion choice in a non-streaming response.
    
    Each choice contains a complete message from the assistant and metadata about
    why the completion finished.
    
    Attributes:
        index: The index of this choice among all choices for the request.
        message: The message generated as the completion.
        finish_reason: The reason why the completion finished - "stop", 
            "length", "tool_calls", "content_filter", or "function_call".
    """
    index: int
    message: ChatMessage
    finish_reason: Optional[Literal["stop", "length", "tool_calls", "content_filter", "function_call"]] = None


class ChatCompletion(BaseModel):
    """
    Represents a complete non-streaming response from the chat completions API.
    
    This is the top-level response object for non-streaming requests, containing
    one or more completion choices along with metadata.
    
    Attributes:
        id: Unique identifier for the completion.
        object: The object type, always "chat.completion".
        created: Unix timestamp of when the completion was created.
        model: The model used for completion.
        choices: List of completion choices.
        usage: Token usage statistics for the request.
        system_fingerprint: System fingerprint for the model.
    """
    id: str
    object: Literal["chat.completion"] = "chat.completion"
    created: int
    model: str
    choices: List[ChatCompletionChoice]
    usage: Optional[UsageInfo] = None
    system_fingerprint: Optional[str] = None


# Streaming Structures

class ChatCompletionChunkChoiceDelta(BaseModel):
    """
    Represents a delta/update for a streaming chat completion.
    
    Rather than providing the entire message at once, streaming responses send
    incremental updates with partial content, which this class models.
    
    Attributes:
        role: The role of the message, typically only in the first chunk.
        content: A piece of the content being streamed.
        tool_calls: Partial tool call information.
    """
    role: Optional[Literal["system", "user", "assistant", "tool"]] = None
    content: Optional[str] = None
    tool_calls: Optional[List[Dict[str, Any]]] = None # Placeholder for tool call structure


class ChatCompletionChunkChoice(BaseModel):
    """
    Represents a single choice in a streaming chat completion chunk.
    
    Similar to ChatCompletionChoice, but for streaming responses where information
    is provided incrementally.
    
    Attributes:
        index: The index of this choice among all choices for the request.
        delta: The delta/update for this chunk.
        finish_reason: The reason why the completion finished, if this is
            the final chunk - "stop", "length", "tool_calls", "content_filter", or "function_call".
        logprobs: Log probabilities for token generation.
    """
    index: int
    delta: ChatCompletionChunkChoiceDelta
    finish_reason: Optional[Literal["stop", "length", "tool_calls", "content_filter", "function_call"]] = None
    logprobs: Optional[Dict[str, Any]] = None # Placeholder if logprobs needed


class ChatCompletionChunk(BaseModel):
    """
    Represents a single chunk in a streaming chat completion response.
    
    This is the top-level object for each chunk in a streaming response, containing
    one or more choice deltas along with metadata.
    
    Attributes:
        id: Unique identifier for the completion (same across chunks).
        object: The object type, always "chat.completion.chunk".
        created: Unix timestamp of when the chunk was created.
        model: The model used for completion.
        choices: List of choice deltas for this chunk.
        usage: Token usage statistics (typically only in the final chunk).
        system_fingerprint: System fingerprint for the model.
    """
    id: str
    object: Literal["chat.completion.chunk"] = "chat.completion.chunk"
    created: int
    model: str
    choices: List[ChatCompletionChunkChoice]
    usage: Optional[UsageInfo] = None # Often included in the *last* chunk in practice
    system_fingerprint: Optional[str] = None


# Request Structure

class ChatCompletionRequest(BaseModel):
    """
    Represents a request to the chat completions API.
    
    This model defines all the parameters that can be included in a request
    to generate a chat completion, including required fields like model and messages,
    as well as optional parameters to control generation.
    
    Attributes:
        model: The model to use for completion.
        messages: The conversation context to generate from.
        temperature: Sampling temperature, between 0 and 2. Higher values like 0.8 make output
            more random, while lower values like 0.2 make it more deterministic.
        top_p: Nucleus sampling parameter, between 0 and 1. An alternative to
            temperature, setting top_p to 0.1 means only considering tokens with the top 10%
            probability mass.
        n: Number of chat completion choices to generate.
        stream: Whether to stream the response or return it all at once.
        stop: Sequences where the API will stop generating further tokens.
        max_tokens: Maximum number of tokens to generate.
        presence_penalty: Penalty between -2.0 and 2.0 for new tokens based on
            whether they appear in the text so far.
        frequency_penalty: Penalty between -2.0 and 2.0 for new tokens based on
            their frequency in the text so far.
        logit_bias: Maps tokens to bias values to adjust likelihood.
        user: A unique identifier representing your end-user.
    """
    model: str
    messages: List[ChatMessage]
    temperature: Optional[float] = 1.0
    top_p: Optional[float] = 1.0
    n: Optional[int] = 1
    stream: Optional[bool] = False
    stop: Optional[Union[str, List[str]]] = None
    max_tokens: Optional[int] = None
    presence_penalty: Optional[float] = 0.0
    frequency_penalty: Optional[float] = 0.0
    logit_bias: Optional[Dict[str, float]] = None
    user: Optional[str] = None
    # Additional parameters like functions, tools, etc. can be added here
    # tools: Optional[List[Dict]] = None
    # tool_choice: Optional[Union[str, Dict]] = None