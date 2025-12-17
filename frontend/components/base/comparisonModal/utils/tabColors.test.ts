import { getTabColorClasses } from './tab-colors';

describe('getTabColorClasses', () => {
  it('should return active classes when isActive is true', () => {
    const result = getTabColorClasses('test', true);
    expect(result).toContain('border-text-information');
    expect(result).toContain('text-text');
  });

  it('should return inactive classes when isActive is false', () => {
    const result = getTabColorClasses('test', false);
    expect(result).toContain('border-transparent');
    expect(result).toContain('text-text-disabled');
    expect(result).toContain('hover:text-gray-300');
  });

  it('should handle different keys', () => {
    const result1 = getTabColorClasses('key1', true);
    const result2 = getTabColorClasses('key2', true);
    expect(result1).toBe(result2); // Should be the same for active
  });
});
