# 📊 PSI Verifier Dashboard Creation README

Create custom Grafana dashboards for your PSI Verifier applications with **automatic data fetching from Loki**. No manual data upload required - dashboards automatically extract runtime logs via pre-configured datasources.

## 🚀 Quick Start (5 Minutes)

### Prerequisites
- Grafana, Loki, and Prometheus running
- Loki datasource pre-configured using `datasources.yml` with datasource set as `loki`
- Your application using PSI Verifier observability package

### Setup Steps
1. **Access Grafana**: `http://localhost:3000` (admin/admin)
2. **Verify Data**: Dashboard automatically fetches live data from Loki
3. **Import Template** (optional): Use `sample_dashboard.json` as starting point
4. **Start Monitoring**: View real-time logs and metrics immediately

## 🔄 How Automatic Data Fetching Works

Your dashboard setup automatically:
- **Extracts runtime logs** from Loki as they're generated
- **Connects via pre-configured datasources** (`datasources.yml` with `loki` datasource)
- **Updates panels in real-time** without manual intervention
- **Populates variables dynamically** from current log data

**Key Benefits:**
- No JSON file uploads needed
- Real-time data visualization
- Automatic field extraction from live logs
- Dynamic dashboard updates as applications run

## 📊 Essential Dashboard Components

### Variables (Dynamic Filtering)
Create variables that automatically populate from live data:

```json
{
  "name": "service_name",
  "type": "query",
  "query": "label_values(service_name)",
  "datasource": {"type": "loki", "uid": "Loki"}
}
```

**Key Variables:**
- `service_name` - Filter by service (from runtime logs)
- `log_level` - Filter by DEBUG, INFO, WARNING, ERROR
- `event_context` - Filter by workflow, training, evaluation, langgraph

### Panel Types

#### Stat Panel - Single Metrics
```logql
sum(count_over_time({service_name=~"$service_name"} [$__range]))
```

#### Gauge Panel - Rates & Percentages
```logql
sum(count_over_time({service_name=~"$service_name", level="ERROR"} [$__range])) / 
sum(count_over_time({service_name=~"$service_name"} [$__range])) * 100
```

#### Pie Chart - Distribution Analysis
```logql
sum by (level)(count_over_time({service_name=~"$service_name"} [$__range]))
```

#### Time Series - Trends
```logql
sum by (level)(rate({service_name=~"$service_name"} [$time_range]))
```

#### Logs Panel - Raw Data
```logql
{service_name=~"$service_name", level="ERROR"} | json
```

## 🎯 LogQL Query Examples

All queries work with **real-time data automatically fetched from Loki**:

### Basic Filtering
```logql
# Service filtering (live logs)
{service_name="my_service"}

# Log level filtering (real-time)
{service_name="my_service", level="ERROR"}

# Multiple criteria (live data)
{service_name="my_service", level=~"ERROR|WARNING"}
```

### JSON Field Extraction
```logql
# Extract all JSON fields (automatic)
{service_name="my_service"} | json

# Filter by extracted field (real-time)
{service_name="my_service"} | json | event_context="workflow"

# Nested field extraction (runtime logs)
{service_name="my_service"} | json | brick_server_result_status="success"
```

### Aggregations & Counting
```logql
# Count logs (live data)
sum(count_over_time({service_name="my_service"} [$__range]))

# Count by field (automatically extracted)
sum by (level)(count_over_time({service_name="my_service"} [$__range]))

# Calculate rates (real-time)
sum by (level)(rate({service_name="my_service"} [$time_range]))
```

### Advanced Queries
```logql
# Success rate (real-time computation)
sum(count_over_time({service_name="my_service"} | json | status="success" [$__range])) / 
sum(count_over_time({service_name="my_service"} | json | status=~"success|error" [$__range])) * 100

# Error distribution (live logs)
sum by (error_type)(count_over_time({service_name="my_service", level="ERROR"} | json [$__range]))

# Custom field analysis (runtime data)
sum by (node_name)(count_over_time({service_name="my_service"} | json | event_context="workflow" [$__range]))
```

## 🎨 Event-Specific Dashboards

### Workflow Events
```logql
# Node distribution
sum by (node_name)(count_over_time({service_name="$service_name"} | json | event_context="workflow" [$__range]))

# Status tracking
sum by (status)(count_over_time({service_name="$service_name"} | json | event_context="workflow" [$__range]))
```

### Training Events
```logql
# Reward analysis
sum by (reward_type)(count_over_time({service_name="$service_name"} | json | event_context="training" [$__range]))

# Hyperparameter tracking
{service_name="$service_name"} | json | event_context="training" | hyperparams!=""
```

### Evaluation Events
```logql
# KC distribution
sum by (generation_kc)(count_over_time({service_name="$service_name"} | json | event_context="evaluation" [$__range]))

# Dataset analysis
sum by (dataset_info)(count_over_time({service_name="$service_name"} | json | event_context="evaluation" [$__range]))
```

## 🔧 Customization Guide

### Adding New Panels
1. **Edit Dashboard** → **Add Panel**
2. **Select Data Source**: Loki (pre-configured for automatic data fetching)
3. **Write LogQL Query**: Use examples above - they work with live data
4. **Configure Visualization**: Colors, thresholds, units
5. **Save Panel** - immediately displays real-time data

### Creating Custom Variables
1. **Dashboard Settings** → **Variables** → **Add Variable**
2. **Configure**:
   - **Name**: `my_custom_var`
   - **Type**: `Query`
   - **Query**: `label_values({service_name="my_service"}, my_field)`
   - **Datasource**: `Loki` (automatically fetches values from live logs)
3. **Use in Queries**: `{service_name="my_service", my_field=~"$my_custom_var"}`
4. **Automatic Updates**: Variables refresh as new log data arrives

### Custom Field Mapping
```logql
# Extract nested fields
{service_name="my_service"} | json | brick_server_result_return_code="0"

# Multi-level nesting
{service_name="my_service"} | json | hyperparams_learning_rate="0.001"
```

## 🐛 Troubleshooting

### No Data Displayed
```bash
# Verify logs reaching Loki automatically
curl -G "http://localhost:3100/loki/api/v1/query" \
  --data-urlencode 'query={service_name="my_service"}' \
  --data-urlencode 'limit=5'

# Check real-time logs
curl -G "http://localhost:3100/loki/api/v1/query_range" \
  --data-urlencode 'query={service_name!=""}' \
  --data-urlencode 'start=1h' \
  --data-urlencode 'end=now'
```

**Check:**
- Application is running and generating logs
- Observability package properly configured
- Logs being sent to Loki in real-time
- Datasource configuration correct

### Query Errors
- Verify field names in live log stream
- Check LogQL syntax for runtime data
- Ensure proper time ranges
- Confirm fields exist in current logs

### Variable Issues
- Check datasource configuration for live data
- Verify query matches runtime log structure
- Ensure logs contain expected fields
- Confirm application is actively logging

## 🔍 Best Practices

### Performance
- Use appropriate time ranges (`$__range`, `$time_range`)
- Add specific filters for large log volumes
- Optimize queries for real-time data
- Consider sampling for large datasets

### Dashboard Organization
- Group related panels with **Row** panels
- Use consistent naming conventions
- Add panel descriptions
- Set meaningful legends and labels

### Variables
- Create reusable variables for common filters
- Use multi-select for flexibility
- Set sensible defaults
- Leverage automatic population from live data

### Visual Design
- Use consistent color schemes
- Set appropriate thresholds for gauges
- Configure alerts for critical metrics
- Enable auto-refresh for real-time updates

## 📈 Sample Dashboard Structure

```json
{
  "title": "PSI Verifier - Service Monitor",
  "panels": [
    {
      "title": "Total Logs",
      "type": "stat",
      "targets": [{"expr": "sum(count_over_time({service_name=\"$service_name\"} [$__range]))"}]
    },
    {
      "title": "Error Rate",
      "type": "gauge",
      "targets": [{"expr": "sum(count_over_time({service_name=\"$service_name\", level=\"ERROR\"} [$__range])) / sum(count_over_time({service_name=\"$service_name\"} [$__range])) * 100"}]
    },
    {
      "title": "Event Distribution",
      "type": "piechart",
      "targets": [{"expr": "sum by (event_context)(count_over_time({service_name=\"$service_name\"} | json [$__range]))"}]
    },
    {
      "title": "Live Logs",
      "type": "logs",
      "targets": [{"expr": "{service_name=\"$service_name\"} | json"}]
    }
  ]
}
```

## 🚀 Next Steps

1. **Access Grafana** - View automatically fetched logs
2. **Import Sample Dashboard** - Use as template (optional)
3. **Customize Panels** - Add your specific metrics using live data
4. **Set Up Alerts** - Configure notifications based on runtime logs
5. **Monitor & Iterate** - Continuously improve based on real-time insights

## 📚 Quick Reference

### Key URLs
- **Grafana**: `http://localhost:3000`
- **Loki**: `http://localhost:3100`
- **Loki Query**: `http://localhost:3100/loki/api/v1/query`

### Essential Variables
- `$service_name` - Filter by service
- `$log_level` - Filter by log level
- `$event_context` - Filter by event type
- `$__range` - Time range for queries
- `$time_range` - Time range for rates

### Common Fields
- `service_name` - Service identifier
- `level` - Log level (DEBUG, INFO, WARNING, ERROR)
- `event_context` - Event type (workflow, training, evaluation, langgraph)
- `node_name` - Workflow node
- `status` - Operation status
- `generation_kc` - Knowledge component
- `dataset_info` - Dataset information

---

**Ready to Start?** Access your Grafana instance and start monitoring your PSI Verifier applications with automatically fetched real-time data! 