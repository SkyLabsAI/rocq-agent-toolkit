"""
HTTP request extractor for web frameworks.

This extractor understands HTTP requests and responses from popular
Python web frameworks like Flask, FastAPI, Django, etc.
It extracts standard HTTP attributes for tracing.
"""

from typing import Any, Callable, Dict, Optional, Tuple

from .base import AttributeExtractor


def _safe_str(value: Any, max_length: int = 1000) -> Optional[str]:
    """Safely convert value to string with length limit."""
    if value is None:
        return None
    try:
        result = str(value)
        return result[:max_length] if len(result) > max_length else result
    except Exception:
        return None


class HttpExtractor(AttributeExtractor):
    """
    Extractor for HTTP requests from web frameworks.

    Supports:
    - Flask: request object
    - FastAPI: Request object
    - Django: HttpRequest object
    - Any object with standard HTTP attributes

    Example usage:
        @trace(extractor="http")
        def create_user(request):
            return {"user_id": "123"}

        @trace(extractor=HttpExtractor(include_headers=True))
        def get_user(request, user_id):
            return get_user_by_id(user_id)
    """

    def __init__(
        self,
        request_arg: str = "request",
        include_headers: bool = False,
        include_query_params: bool = True,
        sensitive_headers: Optional[list] = None,
    ):
        """
        Initialize HTTP extractor.

        Args:
            request_arg: Name of the request argument in function signature
            include_headers: Whether to include HTTP headers in attributes
            include_query_params: Whether to include query parameters
            sensitive_headers: List of header names to exclude (case-insensitive)
        """
        self.request_arg = request_arg
        self.include_headers = include_headers
        self.include_query_params = include_query_params
        self.sensitive_headers = {
            h.lower()
            for h in (
                sensitive_headers
                or [
                    "authorization",
                    "cookie",
                    "set-cookie",
                    "x-api-key",
                    "x-auth-token",
                ]
            )
        }

    def extract_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Extract HTTP attributes from request object."""
        request = self._find_request(func, args, kwargs)
        if not request:
            return {}

        attrs = {}

        # Basic HTTP attributes
        method = getattr(request, "method", None)
        if method:
            attrs["http.method"] = method

        # URL information
        url = (
            getattr(request, "url", None)
            or getattr(request, "build_absolute_uri", lambda: None)()
        )
        if url:
            attrs["http.url"] = _safe_str(url)

        # Path information
        path = getattr(request, "path", None) or getattr(request, "path_info", None)
        if path:
            attrs["http.target"] = _safe_str(path)

        # Host information
        host = getattr(request, "get_host", lambda: None)()
        if not host:
            host = getattr(request, "host", None)
        if host:
            attrs["http.host"] = _safe_str(host)

        # Scheme
        scheme = (
            getattr(request, "scheme", None)
            or getattr(request, "is_secure", lambda: None)()
        )
        if scheme is True:
            attrs["http.scheme"] = "https"
        elif scheme is False:
            attrs["http.scheme"] = "http"
        elif scheme:
            attrs["http.scheme"] = _safe_str(scheme)

        # Remote address
        remote_addr = self._get_remote_addr(request)
        if remote_addr:
            attrs["http.client_ip"] = remote_addr

        # Query parameters
        if self.include_query_params:
            query_params = self._get_query_params(request)
            if query_params:
                attrs["http.query_string"] = query_params

        # Headers
        if self.include_headers:
            headers = self._get_headers(request)
            for key, value in headers.items():
                if key.lower() not in self.sensitive_headers:
                    attrs[f"http.request.header.{key.lower()}"] = _safe_str(value)

        # User agent (commonly used)
        user_agent = self._get_user_agent(request)
        if user_agent:
            attrs["http.user_agent"] = _safe_str(user_agent)

        return {k: v for k, v in attrs.items() if v is not None}

    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Generate span name from HTTP method and endpoint."""
        request = self._find_request(func, args, kwargs)
        if not request:
            return f"HTTP {func.__name__}"

        method = getattr(request, "method", "GET")

        # Try to get endpoint name
        endpoint = None

        # Flask: request.endpoint
        if hasattr(request, "endpoint") and request.endpoint:
            endpoint = request.endpoint
        # FastAPI: request.url.path or route
        elif hasattr(request, "url") and hasattr(request.url, "path"):
            endpoint = request.url.path
        # Django: request.resolver_match
        elif hasattr(request, "resolver_match") and request.resolver_match:
            endpoint = getattr(request.resolver_match, "url_name", None)
        # Fallback to function name
        else:
            endpoint = func.__name__

        return f"HTTP {method} {endpoint}"

    def get_metrics_labels(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, str]:
        """Generate metrics labels for HTTP operations."""
        request = self._find_request(func, args, kwargs)
        labels = {"operation": func.__name__}

        if request:
            method = getattr(request, "method", None)
            if method:
                labels["method"] = method

            # Add endpoint if available
            path = getattr(request, "path", None)
            if path:
                # Normalize path for metrics (remove IDs, etc.)
                normalized_path = self._normalize_path_for_metrics(path)
                labels["endpoint"] = normalized_path

        return labels

    def _find_request(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]):
        """Find the request object in function arguments."""
        # Check kwargs first
        if self.request_arg in kwargs:
            return kwargs[self.request_arg]

        # For methods, skip 'self' parameter
        if args and hasattr(args[0], "__dict__") and len(args) > 1:
            return args[1]  # Assume request is first argument after self
        elif args:
            return args[0]  # Assume request is first argument

        return None

    def _get_remote_addr(self, request) -> Optional[str]:
        """Get remote IP address from request."""
        # Try common attributes for remote address
        for attr in ["remote_addr", "client", "environ"]:
            if hasattr(request, attr):
                addr = getattr(request, attr)
                if isinstance(addr, str):
                    return addr
                elif hasattr(addr, "host"):  # FastAPI client
                    return addr.host
                elif isinstance(addr, dict) and "REMOTE_ADDR" in addr:  # WSGI environ
                    return addr["REMOTE_ADDR"]

        return None

    def _get_query_params(self, request) -> Optional[str]:
        """Get query parameters from request."""
        # Try different ways to get query string
        query_string = None

        if hasattr(request, "query_string"):
            qs = request.query_string
            if isinstance(qs, bytes):
                query_string = qs.decode("utf-8", errors="ignore")
            else:
                query_string = str(qs)
        elif hasattr(request, "GET") and request.GET:  # Django
            query_string = request.GET.urlencode()
        elif hasattr(request, "args") and request.args:  # Flask
            query_string = str(request.args)
        elif hasattr(request, "query_params"):  # FastAPI
            query_string = str(request.query_params)

        return query_string if query_string else None

    def _get_headers(self, request) -> Dict[str, str]:
        """Get headers from request."""
        headers = {}

        if hasattr(request, "headers"):
            # Most frameworks
            if hasattr(request.headers, "items"):
                headers = dict(request.headers.items())
            elif isinstance(request.headers, dict):
                headers = request.headers
        elif hasattr(request, "META"):
            # Django
            for key, value in request.META.items():
                if key.startswith("HTTP_"):
                    header_name = key[5:].replace("_", "-").lower()
                    headers[header_name] = str(value)

        return headers

    def _get_user_agent(self, request) -> Optional[str]:
        """Get user agent from request."""
        # Try different ways to get user agent
        if hasattr(request, "headers") and "user-agent" in request.headers:
            return request.headers["user-agent"]
        elif hasattr(request, "META") and "HTTP_USER_AGENT" in request.META:
            return request.META["HTTP_USER_AGENT"]
        elif hasattr(request, "user_agent"):
            ua = request.user_agent
            return str(ua) if ua else None

        return None

    def _normalize_path_for_metrics(self, path: str) -> str:
        """Normalize URL path for metrics to avoid high cardinality."""
        # Simple normalization: replace numeric segments with placeholders
        import re

        # Replace UUIDs
        path = re.sub(
            r"/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}",
            "/{uuid}",
            path,
            flags=re.IGNORECASE,
        )

        # Replace numeric IDs
        path = re.sub(r"/\d+", "/{id}", path)

        return path
