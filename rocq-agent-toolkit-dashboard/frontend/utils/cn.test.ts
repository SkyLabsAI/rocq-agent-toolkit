import { cn } from './cn';

describe('cn', () => {
  it('should merge class names', () => {
    const result = cn('class1', 'class2');
    expect(result).toContain('class1');
    expect(result).toContain('class2');
  });

  it('should handle conditional classes', () => {
    const result = cn('base', true && 'conditional');
    expect(result).toContain('base');
    expect(result).toContain('conditional');
  });

  it('should handle arrays', () => {
    const result = cn(['class1', 'class2']);
    expect(result).toContain('class1');
    expect(result).toContain('class2');
  });

  it('should handle objects', () => {
    const result = cn({ class1: true, class2: false });
    expect(result).toContain('class1');
    expect(result).not.toContain('class2');
  });

  it('should merge Tailwind conflicts', () => {
    const result = cn('p-4', 'p-6');
    // tailwind-merge should resolve this to just p-6
    expect(result).toBe('p-6');
  });

  it('should handle empty inputs', () => {
    const result = cn();
    expect(result).toBe('');
  });

  it('should handle mixed inputs', () => {
    const result = cn('base', ['array1', 'array2'], { conditional: true });
    expect(result).toContain('base');
    expect(result).toContain('array1');
    expect(result).toContain('array2');
    expect(result).toContain('conditional');
  });
});
