import { RunTaskCell } from '@/features/compare';
import { ComparisonRow } from './comparison-row';
import { TaskRowData } from '../../../utils';

export const TaskDetailsTable = ({
  id,
  details,
  taskRowData,
}: {
  id: string;
  details: RunTaskCell[];
  taskRowData: TaskRowData;
}) => {
  const metricRows = extractMetricRows(taskRowData);

  return (
    <>
      <div className='py-2 divide-y divide-elevation-surface-overlay'>
        {metricRows.map(row => (
          <ComparisonRow key={row.key} label={row.label} values={row.values} />
        ))}
      </div>
    </>
  );
};

// --- Helper 1: Flatten nested objects into dot-notation keys ---
// Input: { token_counts: { total: 10, input: 5 } }
// Output: ["token_counts.total", "token_counts.input"]
function getFlatKeys(obj: any, prefix = ''): string[] {
  if (!obj || typeof obj !== 'object') return [];

  return Object.keys(obj).reduce((acc: string[], key) => {
    const newPath = prefix ? `${prefix}.${key}` : key;

    if (
      typeof obj[key] === 'object' &&
      obj[key] !== null &&
      !Array.isArray(obj[key]) // Don't flatten arrays, treat them as values
    ) {
      acc.push(...getFlatKeys(obj[key], newPath));
    } else {
      acc.push(newPath);
    }
    return acc;
  }, []);
}

// --- Helper 2: Deep Value Accessor ---
// Input: (taskObject, "metrics.token_counts.total")
// Output: 10 or undefined
function getNestedValue(obj: any, path: string): any {
  return path
    .split('.')
    .reduce((acc, part) => (acc ? acc[part] : undefined), obj);
}

// --- Main Interface for your Table Row ---
export interface MetricRowOutput {
  key: string; // e.g. "token_counts.total_tokens"
  label: string; // e.g. "Token Counts Total Tokens" (Formatted)
  values: string[]; // ["100", "-", "200"]
}

/**
 * Main Function: Extracts all metric rows from a TaskRowData
 */
export function extractMetricRows(rowData: TaskRowData): MetricRowOutput[] {
  // 1. Discover ALL unique keys present across ALL runs for this task
  // We scan every cell because Run A might have a custom metric that Run B lacks.
  const allMetricKeys = new Set<string>();

  rowData.cells.forEach(cell => {
    if (cell && cell.task && cell.task.metrics) {
      // Get flattened keys specifically from the 'metrics' object
      const keys = getFlatKeys(cell.task.metrics);
      keys.forEach(k => allMetricKeys.add(k));
    }
  });

  // 2. Sort keys alphabetically for consistent rendering
  const sortedKeys = Array.from(allMetricKeys).sort();

  // 3. Transform into Rows
  return sortedKeys.map(key => {
    const values = rowData.cells.map(cell => {
      // Safety check: Cell or Task might be missing
      if (!cell || !cell.task || !cell.task.metrics) {
        return '-';
      }

      // Extract value
      const val = getNestedValue(cell.task.metrics, key);

      // Handle missing values or rendering objects/arrays
      if (val === undefined || val === null) return '-';
      if (typeof val === 'object') return JSON.stringify(val); // Edge case for arrays
      return String(val);
    });

    return {
      key,
      // Format label: "token_counts.total" -> "Token Counts Total"
      label: key
        .split(/[._]/)
        .map(w => w.charAt(0).toUpperCase() + w.slice(1))
        .join(' '),
      values,
    };
  });
}
