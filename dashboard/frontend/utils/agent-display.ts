/**
 * Utility functions for formatting agent display names.
 *
 * Ensures consistent formatting of agent class and instance names
 * with checksums for disambiguation.
 */

/**
 * Format an agent class display name with checksum.
 *
 * @param cls_name - The agent class name
 * @param cls_checksum - The agent class checksum
 * @returns Formatted display name: "{cls_name}@{first_8_chars_of_checksum}"
 */
export function formatAgentClassDisplayName(
  cls_name: string,
  cls_checksum: string
): string {
  return `${cls_name}@${cls_checksum.slice(0, 8)}...`;
}

/**
 * Format an agent instance display name with checksum.
 *
 * @param name - The agent instance name
 * @param agent_checksum - The agent instance checksum
 * @returns Formatted display name: "{name}@{first_8_chars_of_checksum}"
 */
export function formatAgentInstanceDisplayName(
  name: string,
  agent_checksum: string
): string {
  return `${name}@${agent_checksum.slice(0, 8)}...`;
}

