"""
Database operation extractor.

This extractor understands database operations and extracts standard database
attributes for tracing. It works with any database-related function.
"""

from typing import Any, Callable, Dict, Optional, Tuple

from .base import AttributeExtractor


class DatabaseExtractor(AttributeExtractor):
    """
    Extractor for database operations.

    Supports:
    - SQL operations (SELECT, INSERT, UPDATE, DELETE)
    - NoSQL operations
    - ORM operations (SQLAlchemy, Django ORM, etc.)
    - Any database-related function

    Example usage:
        @trace(extractor="database", system="postgresql", table="users")
        def get_user(user_id):
            return db.query("SELECT * FROM users WHERE id = %s", user_id)

        @trace(extractor=DatabaseExtractor(system="mongodb", collection="products"))
        def find_products(category):
            return db.products.find({"category": category})
    """

    def __init__(
        self,
        system: str = "sql",
        table: Optional[str] = None,
        collection: Optional[str] = None,
        operation: Optional[str] = None,
        database_name: Optional[str] = None,
        include_query: bool = False,
        max_query_length: int = 1000,
    ):
        """
        Initialize database extractor.

        Args:
            system:
                Database system ("sql", "postgresql", "mysql", "mongodb", "redis", etc.)
            table: Table name for SQL operations
            collection: Collection name for NoSQL operations
            operation:
                Database operation ("select", "insert", "update", "delete", "find", etc)
            database_name: Name of the database
            include_query:
                Whether to include query text in spans (be careful with sensitive data)
            max_query_length: Maximum length for query text
        """
        self.system = system
        self.table = table
        self.collection = collection
        self.operation = operation
        self.database_name = database_name
        self.include_query = include_query
        self.max_query_length = max_query_length

    def extract_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Extract database attributes from function call."""
        attrs = {
            "db.system": self.system,
        }

        # Add database name
        if self.database_name:
            attrs["db.name"] = self.database_name

        # Determine operation
        operation = self.operation
        if not operation:
            operation = self._infer_operation(func)

        if operation:
            attrs["db.operation"] = operation

        # Add table/collection information
        if self.table:
            attrs["db.sql.table"] = self.table
        elif self.collection:
            attrs["db.mongodb.collection"] = self.collection

        # Try to extract query information if requested
        if self.include_query:
            query_info = self._extract_query_info(args, kwargs)
            if query_info:
                attrs.update(query_info)

        # Add connection information if available
        connection_info = self._extract_connection_info(args, kwargs)
        if connection_info:
            attrs.update(connection_info)

        return attrs

    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Generate span name for database operation."""
        operation = self.operation or self._infer_operation(func)
        target = self.table or self.collection or "table"

        if operation:
            return f"db.{operation}.{target}"
        else:
            return f"db.{func.__name__}"

    def get_metrics_labels(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, str]:
        """Generate metrics labels for database operations."""
        labels = {
            "operation": func.__name__,
            "db_system": self.system,
        }

        # Add operation type
        operation = self.operation or self._infer_operation(func)
        if operation:
            labels["db_operation"] = operation

        # Add table/collection
        if self.table:
            labels["table"] = self.table
        elif self.collection:
            labels["collection"] = self.collection

        return labels

    def _infer_operation(self, func: Callable) -> Optional[str]:
        """Infer database operation from function name."""
        func_name = func.__name__.lower()

        # SQL operations
        if any(op in func_name for op in ["create", "insert", "add", "save"]):
            return "insert"
        elif any(
            op in func_name
            for op in ["get", "find", "select", "query", "fetch", "read"]
        ):
            return "select"
        elif any(op in func_name for op in ["update", "modify", "edit", "change"]):
            return "update"
        elif any(op in func_name for op in ["delete", "remove", "drop"]):
            return "delete"

        # NoSQL operations
        elif "count" in func_name:
            return "count"
        elif "aggregate" in func_name:
            return "aggregate"
        elif "index" in func_name:
            return "index"

        return None

    def _extract_query_info(
        self, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Extract query information from function arguments."""
        attrs = {}

        # Look for common query parameter names
        query_params = ["query", "sql", "statement", "filter", "where"]

        for param in query_params:
            if param in kwargs:
                query_value = kwargs[param]
                if isinstance(query_value, str):
                    attrs["db.statement"] = self._truncate_query(query_value)
                break

        # If no named parameter found, check positional arguments
        if "db.statement" not in attrs and args:
            # First string argument might be the query
            for arg in args:
                if isinstance(arg, str) and len(arg) > 10:  # Likely a query
                    attrs["db.statement"] = self._truncate_query(arg)
                    break

        return attrs

    def _extract_connection_info(
        self, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Extract database connection information."""
        attrs = {}

        # Look for connection objects in arguments
        for arg in args:
            if hasattr(arg, "get_dsn_parameters"):
                # This looks like a psycopg2 connection
                try:
                    dsn_params = arg.get_dsn_parameters()
                    if "host" in dsn_params:
                        attrs[
                            "db.connection_string"
                        ] = f"postgresql://{dsn_params['host']}"
                    if "dbname" in dsn_params:
                        attrs["db.name"] = dsn_params["dbname"]
                except Exception:
                    pass
                break
            elif hasattr(arg, "server_info"):
                # This might be a MySQL connection
                try:
                    attrs["db.system"] = "mysql"
                except Exception:
                    pass
                break

        return attrs

    def _truncate_query(self, query: str) -> str:
        """Truncate query to maximum length and sanitize."""
        # Remove extra whitespace
        query = " ".join(query.split())

        if len(query) > self.max_query_length:
            query = query[: self.max_query_length] + "..."

        return query
