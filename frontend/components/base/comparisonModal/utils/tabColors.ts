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
    return {
      'blue': 'border-blue-400 text-blue-400',
      'purple': 'border-purple-400 text-purple-400',
      'green': 'border-green-400 text-green-400',
      'orange': 'border-orange-400 text-orange-400',
      'gray': 'border-gray-400 text-gray-400'
    }[color] || '';
  }
  return 'border-transparent text-gray-400 hover:text-gray-300';
}
