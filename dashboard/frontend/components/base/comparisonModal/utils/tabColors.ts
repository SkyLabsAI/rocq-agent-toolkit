export function getTabColor(key: string): string {
  const lowerKey = key.toLowerCase();
  if (key === 'tactic') return 'purple';
  if (key === 'tactic_prediction_explanation') return 'blue';
  if (key === 'tactic_prediction_tactic') return 'green';
  if (lowerKey.includes('cpp') || lowerKey.includes('code')) return 'blue';
  if (lowerKey.includes('target')) return 'purple';
  if (lowerKey.includes('lemma')) return 'green';
  if (lowerKey.includes('states')) return 'orange';
  return 'gray';
}

export function getTabColorClasses(key: string, isActive: boolean): string {
  const color = getTabColor(key);
  if (isActive) {
    return 'border-text-information text-text-information';
  }
  return 'border-transparent text-gray-400 hover:text-gray-300';
}
