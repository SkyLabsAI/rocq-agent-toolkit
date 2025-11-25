export function getTabColorClasses(key: string, isActive: boolean): string {
  if (isActive) {
    return 'border-text-information text-text';
  }
  return 'border-transparent text-text-disabled hover:text-gray-300';
}
