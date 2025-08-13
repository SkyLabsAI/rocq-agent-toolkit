# Standard lib
import datetime as dt
import json
from typing import List, Dict, Any, Optional, Tuple, Set

# External
import requests

"""Three-step training data extractor from Loki.

Step 1: Query for verify_node logs to get trace_ids with successful verification
Step 2: For each trace_id, find unique function_mangled_name from spec_artifacts_generator logs
Step 3: For each function, extract the latest training data fields

Usage:
    python extract_training_examples.py > training_data.jsonl

Optionally set the Loki base URL via the environment variable ``LOKI_URL``.
"""

# Stdout / environment helpers
import os, sys

# Where is Loki?
loki = os.getenv("LOKI_URL", "http://172.31.0.1:3100")

# Output file for extracted logs
output_file = os.getenv("OUTPUT_FILE", "psi_verifier/observability/extract_training_data/training_data.jsonl")

def query_loki(query: str, start_time: int, end_time: int, limit: int = 5000) -> List[Dict[str, Any]]:
    """Query Loki and return parsed results."""
    params = {
        "query": query,
        "start": start_time,
        "end": end_time,
        "limit": limit,
        "direction": "BACKWARD",
    }
    
    resp = requests.get(f"{loki}/loki/api/v1/query_range", params=params)
    
    try:
        resp.raise_for_status()
    except requests.HTTPError:
        print("Loki returned an error:\n", resp.text, file=sys.stderr)
        raise
    
    return resp.json()["data"]["result"]

def extract_verify_node_data(streams: List[Dict[str, Any]]) -> List[str]:
    """Extract trace_ids from verify_node logs (return_code filtering now done in query)."""
    verify_data: List[str] = []
    
    for stream in streams:
        for _, line in stream["values"]:
            try:
                entry = json.loads(line)
                if entry.get("node_name") == "verify_node":
                    trace_id = entry.get("trace_id")
                    return_code = entry.get("command_execution_result.return_code")
                    
                    # Since filtering is now done in query, we just need to check for trace_id
                    if trace_id:
                        verify_data.append(trace_id)
                        print(f"Found verify_node with trace_id: {trace_id[:50]}... (return_code: {return_code})")
            except json.JSONDecodeError:
                continue
    
    return verify_data

def extract_function_names_for_trace_id(trace_id: str, start_time: int, end_time: int) -> List[str]:
    """Extract unique function_mangled_name values for a given trace_id from spec_artifacts_generator logs."""
    # Query for spec_artifacts_generator logs with this specific trace_id and successful return code
    spec_artifacts_query = f'{{service_name="Production_Server_v3"}} | json | trace_id="{trace_id}" | node_name="spec_artifacts_generator" | command_execution_result_return_code=0'
    
    try:
        streams = query_loki(spec_artifacts_query, start_time, end_time)
        
        function_names: List[str] = []
        seen_functions: Set[str] = set()
        
        for stream in streams:

            for _, line in stream["values"]:
                try:
                    entry = json.loads(line)
                    
                    # Ensure this log has the exact trace_id we're looking for
                    if entry.get("trace_id") != trace_id:
                        continue
                    
                    # Ensure this is a spec_artifacts_generator log with successful return code
                    if (entry.get("node_name") == "spec_artifacts_generator" and 
                        entry.get("command_execution_result.return_code") == 0):
                        
                        function_name = entry.get("function_mangled_name")
                        if function_name and function_name not in seen_functions:
                            function_names.append(function_name)
                            seen_functions.add(function_name)
                            print(f"Found function: {function_name} for trace_id: {trace_id[:50]}...")
                            
                except json.JSONDecodeError:
                    continue
        
        return function_names
        
    except Exception as e:
        print(f"Error querying for function names in trace_id '{trace_id}': {e}", file=sys.stderr)
        return []

def extract_all_data_for_function(trace_id: str, function_name: str, start_time: int, end_time: int) -> Optional[Dict[str, Any]]:
    """Extract all required fields for a given trace_id and function_mangled_name, getting the latest entry for each field type."""
    # Query for ALL logs with this specific trace_id and function_mangled_name
    function_query = f'{{service_name="Production_Server_v3"}} | json | trace_id="{trace_id}" | function_mangled_name="{function_name}"'
    
    try:
        streams = query_loki(function_query, start_time, end_time)
        
        # Collect all data fields from all logs with this trace_id and function_name
        result_data: Dict[str, Any] = {
            "trace_id": trace_id,
            "function_mangled_name": function_name,
            "timestamp": None,
        }
        
        # Track the latest timestamp for each field type
        latest_timestamps: Dict[str, int] = {}
        
        for stream in streams:
            for ts, line in stream["values"]:
                try:
                    entry = json.loads(line)
                    
                    # Ensure this log has the exact trace_id and function_name we're looking for
                    if (entry.get("trace_id") != trace_id or 
                        entry.get("function_mangled_name") != function_name):
                        continue
                    
                    # Convert timestamp to int for comparison (ts might be string)
                    try:
                        timestamp = int(ts)
                    except (ValueError, TypeError):
                        continue
                    
                    # Extract all fields we're interested in
                    fields_to_extract = [
                        "cpp_code", "structured_il_spec", "full_nl_spec", 
                        "specification_goals", "spec"
                    ]
                    
                    for field in fields_to_extract:
                        if field in entry:
                            # Only update if this is the latest timestamp for this field
                            if field not in latest_timestamps or timestamp > latest_timestamps[field]:
                                result_data[field] = entry[field]
                                latest_timestamps[field] = timestamp
                                
                                # Update overall timestamp to the latest we've seen
                                if result_data["timestamp"] is None or timestamp > int(result_data["timestamp"] or 0):
                                    result_data["timestamp"] = ts
                    
                    # Extract command execution results from spec_artifacts_generator entries
                    if entry.get("node_name") == "spec_artifacts_generator":
                        cmd_results = {
                            "return_code": entry.get("command_execution_result.return_code"),
                            "stdout": entry.get("command_execution_result.stdout"),
                            "stderr": entry.get("command_execution_result.stderr"),
                            "is_ok": entry.get("command_execution_result.is_ok")
                        }
                        
                        if any(v is not None for v in cmd_results.values()):
                            # Only update if this is the latest spec_artifacts_generator entry
                            if "command_execution_results" not in latest_timestamps or timestamp > latest_timestamps.get("command_execution_results", 0):
                                result_data["command_execution_results"] = cmd_results
                                latest_timestamps["command_execution_results"] = timestamp
                     
                except json.JSONDecodeError:
                    continue
        
        # Return the collected data if we found any relevant fields
        if len(result_data) > 3:  # More than just trace_id, function_name, and timestamp
            return result_data
            
    except Exception as e:
        print(f"Error querying for function '{function_name}' in trace_id '{trace_id}': {e}", file=sys.stderr)
    
    return None

# Main execution
if __name__ == "__main__":
    # Timespan: last 24 hours in nanoseconds since epoch (UTC)
    now = dt.datetime.now(dt.timezone.utc)
    start = int((now - dt.timedelta(hours=200)).timestamp() * 1e9)
    end = int(now.timestamp() * 1e9)
    
    print("Step 1: Querying for verify_node logs...")
    
    # Step 1: Get verify_node logs
    verify_query = '{service_name="Production_Server_v3"} | json | node_name="verify_node" | command_execution_result_return_code="0"'
    verify_streams = query_loki(verify_query, start, end)
    
    # Extract trace_ids
    trace_ids = extract_verify_node_data(verify_streams)
    print(f"Found {len(trace_ids)} verify_node entries")
    
    if not trace_ids:
        print("No verify_node data found. Exiting.")
        sys.exit(0)
    
    print("Step 2: Finding unique function names for each trace_id...")
    
    # Step 2: For each trace_id, find unique function names
    trace_id_functions: List[Tuple[str, str]] = []  # List of (trace_id, function_name) pairs
    processed_trace_ids = set(trace_ids)  # Convert to set to avoid duplicates
    
    for trace_id in processed_trace_ids:
        print(f"Finding functions for trace_id: {trace_id[:50]}...")
        
        # Get unique function names for this trace_id
        function_names = extract_function_names_for_trace_id(trace_id, start, end)
        
        if function_names:
            for function_name in function_names:
                trace_id_functions.append((trace_id, function_name))
            print(f"✓ Found {len(function_names)} functions for trace_id: {trace_id[:50]}")
        else:
            print(f"✗ No functions found for trace_id: {trace_id[:50]}")
    
    print(f"Step 3: Extracting training data for {len(trace_id_functions)} functions...")
    
    # Step 3: For each function, extract the training data
    training_examples: List[Dict[str, Any]] = []
    
    for trace_id, function_name in trace_id_functions:
        print(f"Extracting data for function: {function_name[:50]}... in trace_id: {trace_id[:50]}...")
        
        # Extract all data for this specific function
        complete_data = extract_all_data_for_function(trace_id, function_name, start, end)
        
        if complete_data:
            training_examples.append(complete_data)
            print(f"✓ Found data for function: {function_name[:50]}")
        else:
            print(f"✗ No data found for function: {function_name[:50]}")
    
    print(f"Step 4: Writing {len(training_examples)} complete training examples to {output_file}")
    
    # Write results to file
    with open(output_file, 'w', encoding='utf-8') as f:
        for example in training_examples:
            # Write as JSON lines format
            f.write(json.dumps(example, ensure_ascii=False) + '\n')
    
    print(f"Successfully extracted {len(training_examples)} training examples to {output_file}")
