# API Specification for TaskSet Features

This document outlines the APIs required for the taskset details and filtering features.

## Base URL
All APIs use the base URL from `config.DATA_API` environment variable.

---

## 1. Get All TaskSets

**Endpoint:** `GET /tasksets`

**Description:** Returns a list of all tasksets.

**Response:** Array of `TaskSet` objects

**Response Schema:**
```typescript
interface TaskSet {
  id: string;        // Unique identifier for the taskset
  name: string;             // Display name of the taskset
  description?: string;     // Optional description
  created_at: string;       // ISO 8601 timestamp
}
```

**Example Response:**
```json
[
  {
    "id": "taskset_001",
    "name": "Mathematical Proofs",
    "description": "A comprehensive collection of mathematical theorem proving tasks",
    "created_at": "2025-11-07T00:00:00.000Z"
  }
]
```

---

## 2. Get TaskSet Datasets

**Endpoint:** `GET /tasksets/{tasksetId}/datasets`

**Description:** Returns all datasets (benchmarks) associated with a taskset.

**Path Parameters:**
- `tasksetId` (string): The taskset identifier

**Response:** Array of `Benchmark` objects

**Response Schema:**
```typescript
interface Benchmark {
  dataset_id: string;       // Unique identifier for the dataset/benchmark
  description?: string;     // Optional description
  created_at: string;       // ISO 8601 timestamp
}
```

**Example Response:**
```json
[
  {
    "dataset_id": "benchmark_001",
    "description": "Collection of mathematical theorem proving tasks",
    "created_at": "2025-10-08T00:00:00.000Z"
  }
]
```

---

## 3. Get TaskSet Results (Matrix)

**Endpoint:** `GET /tasksets/{tasksetId}/results`

**Description:** Returns the complete results matrix for a taskset, showing task results across all agent instances. This is the main API for the taskset details page with filtering capabilities.

**Path Parameters:**
- `tasksetId` (string): The taskset identifier

**Response:** `TaskSetResults` object

**Response Schema:**
```typescript
interface TaskSetResults {
  id: string;                    // The taskset identifier
  tasks: TaskSetTask[];                 // Array of all tasks in the taskset
  agent_instances: TaskSetAgentInstance[]; // Array of all agent instances
  results: TaskSetTaskResult[];          // Matrix of results (task × agent_instance)
}

interface TaskSetTask {
  task_id: string;                      // Unique task identifier
  task_kind?: TaskKind;                 // Optional: Type of task (e.g., "FullProofTask")
  dataset_id?: string;                  // Optional: Associated dataset/benchmark ID
  tags?: Record<string, string>;        // **IMPORTANT**: Dynamic tags from API
                                        // Key-value pairs, e.g., {"priority": "high", "difficulty": "hard"}
}

interface TaskSetAgentInstance {
  agent_instance_id: string;            // Unique identifier for the agent instance
  agent_name: string;                   // Display name of the agent
  agent_checksum: string;               // Checksum/hash of the agent instance
  run_id: string;                       // Associated run ID
}

interface TaskSetTaskResult {
  task_id: string;                      // References a task from tasks array
  agent_instance_id: string;            // References an agent_instance from agent_instances array
  success_count: number;                 // Number of successful runs for this task+instance
  total_count: number;                   // Total number of runs for this task+instance
}
```

**Example Response:**
```json
{
  "id": "taskset_001",
  "tasks": [
    {
      "task_id": "task_taskset_001_001",
      "task_kind": "FullProofTask",
      "dataset_id": "benchmark_001",
      "tags": {
        "priority": "high",
        "difficulty": "hard",
        "category": "algebra"
      }
    },
    {
      "task_id": "task_project_001_002",
      "task_kind": "FullProofTask",
      "dataset_id": "benchmark_001",
      "tags": {
        "priority": "medium",
        "difficulty": "medium"
      }
    }
  ],
  "agent_instances": [
    {
      "agent_instance_id": "instance_taskset_001_checksum_001",
      "agent_name": "ProofBot-v2.1",
      "agent_checksum": "checksum_001",
      "run_id": "run_taskset_001_checksum_001_001"
    },
    {
      "agent_instance_id": "instance_taskset_001_checksum_002",
      "agent_name": "MathSolver-Alpha",
      "agent_checksum": "checksum_002",
      "run_id": "run_taskset_001_checksum_002_001"
    }
  ],
  "results": [
    {
      "task_id": "task_taskset_001_001",
      "agent_instance_id": "instance_taskset_001_checksum_001",
      "success_count": 5,
      "total_count": 8
    },
    {
      "task_id": "task_taskset_001_001",
      "agent_instance_id": "instance_taskset_001_checksum_002",
      "success_count": 3,
      "total_count": 7
    },
    {
      "task_id": "task_taskset_001_002",
      "agent_instance_id": "instance_taskset_001_checksum_001",
      "success_count": 6,
      "total_count": 6
    }
  ]
}
```

---

## Important Notes

### Tags Field
- **Tags are dynamic** - They come from the API and can have any key-value pairs
- Tags are used for filtering tasks in the UI
- Tasks may or may not have tags (tags field is optional)
- Tag format: `Record<string, string>` - all values must be strings
- Example tags: `{"priority": "high", "difficulty": "hard", "category": "algebra"}`

### Results Matrix
- The `results` array represents a sparse matrix
- Each entry in `results` corresponds to one cell in the task × agent_instance matrix
- If a task has no runs for a particular agent instance, that combination may be omitted from the results array (or have `total_count: 0`)
- The frontend handles missing entries by showing "-" in the table

### Performance Considerations
- This endpoint may return large datasets (many tasks × many agent instances)
- Consider pagination or filtering if the dataset becomes too large
- The frontend implements client-side filtering for tags and agent instances

---

## 4. Create Dataset from Tasks

**Endpoint:** `POST /datasets`

**Description:** Creates a new dataset (benchmark) from selected tasks in a project.

**Request Body:**
```typescript
{
  name: string;                    // Required: Dataset name
  description?: string;            // Optional: Dataset description
  task_ids: string[];              // Required: Array of task IDs to include
  id: string;             // Required: TaskSet ID these tasks belong to
}
```

**Example Request:**
```json
{
  "name": "High Priority Tasks",
  "description": "A dataset containing all high-priority tasks",
  "task_ids": [
    "task_taskset_001_001",
    "task_taskset_001_002",
    "task_taskset_001_005"
  ],
  "id": "taskset_001"
}
```

**Response:** `Benchmark` object

**Response Schema:**
```typescript
interface Benchmark {
  dataset_id: string;       // Unique identifier for the newly created dataset
  description?: string;      // Dataset description (if provided)
  created_at: string;       // ISO 8601 timestamp
}
```

**Example Response:**
```json
{
  "dataset_id": "benchmark_009",
  "description": "A dataset containing all high-priority tasks",
  "created_at": "2025-01-07T12:00:00.000Z"
}
```

**Status Codes:**
- `201 Created` - Dataset created successfully
- `400 Bad Request` - Invalid request (missing name, empty task_ids, etc.)
- `404 Not Found` - TaskSet not found
- `500 Internal Server Error` - Server error

---

## Related Existing APIs Used

The following existing APIs are also used in the project details flow:

### Get Runs by Agent Instance
**Endpoint:** `GET /agents/instance/{agentChecksum}/runs`

Used when clicking on a task result cell to show available runs for that agent instance.

### Get Task Details
**Endpoint:** `GET /runs/{runId}/tasks/{taskId}/details`

Used to show detailed task results in the modal.

### Get Observability Logs
**Endpoint:** `GET /observability/logs?run_id={runId}&task_id={taskId}`

Used to show observability logs for a task.

---

## Error Handling

All endpoints should return appropriate HTTP status codes:
- `200 OK` - Success
- `404 Not Found` - Project/resource not found
- `500 Internal Server Error` - Server error

Error responses should follow a consistent format:
```json
{
  "error": "Error message",
  "code": "ERROR_CODE"
}
```

