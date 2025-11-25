/**
 * Noto Sans Font Utilities
 * 
 * This file provides utilities for working with Noto Sans fonts in the project.
 * All fonts are preloaded and available as Tailwind CSS variables.
 */

export const notoSansVariants = {
  regular: 'font-noto-sans',
  condensed: 'font-noto-condensed', 
  extraCondensed: 'font-noto-extra-condensed',
} as const;

export const notoSansWeights = {
  thin: 'font-thin',        // 100
  extraLight: 'font-extralight', // 200
  light: 'font-light',      // 300
  normal: 'font-normal',    // 400
  medium: 'font-medium',    // 500
  semibold: 'font-semibold', // 600
  bold: 'font-bold',        // 700
  extrabold: 'font-extrabold', // 800
  black: 'font-black',      // 900
} as const;

/**
 * Utility function to combine Noto Sans variant with weight
 */
export function notoSans(
  variant: keyof typeof notoSansVariants = 'regular',
  weight: keyof typeof notoSansWeights = 'normal'
): string {
  return `${notoSansVariants[variant]} ${notoSansWeights[weight]}`;
}

/**
 * Preset combinations for common use cases
 */
export const notoSansPresets = {
  // Headers
  h1: notoSans('regular', 'bold'),
  h2: notoSans('regular', 'semibold'),
  h3: notoSans('regular', 'medium'),
  
  // Body text
  body: notoSans('regular', 'normal'),
  bodyBold: notoSans('regular', 'medium'),
  
  // UI elements
  button: notoSans('regular', 'medium'),
  label: notoSans('regular', 'medium'),
  caption: notoSans('regular', 'normal'),
  
  // Condensed variants for space-constrained areas
  compactHeader: notoSans('condensed', 'semibold'),
  compactBody: notoSans('condensed', 'normal'),
  ultraCompact: notoSans('extraCondensed', 'normal'),
} as const;

// Type exports for better TypeScript support
export type NotoSansVariant = keyof typeof notoSansVariants;
export type NotoSansWeight = keyof typeof notoSansWeights;
export type NotoSansPreset = keyof typeof notoSansPresets;