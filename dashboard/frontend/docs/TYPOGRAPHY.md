# Noto Sans Typography System

This project uses Google's Noto Sans font family with comprehensive support for variable fonts and static fallbacks. The fonts are configured as Tailwind CSS variables for easy usage throughout the application.

## Available Fonts

### 1. Noto Sans (Regular)
- **Variable Font**: Supports weight 100-900 and width 62.5%-100%
- **Usage**: Primary font for body text, headers, and UI elements
- **Tailwind Class**: `font-noto-sans`

### 2. Noto Sans Condensed  
- **Usage**: Space-constrained layouts, sidebars, cards
- **Tailwind Class**: `font-noto-condensed`

### 3. Noto Sans Extra Condensed
- **Usage**: Ultra-compact layouts, tables, dense information
- **Tailwind Class**: `font-noto-extra-condensed`

## Font Weights Available

| Weight | Tailwind Class | Numeric Value |
|--------|----------------|---------------|
| Thin | `font-thin` | 100 |
| Extra Light | `font-extralight` | 200 |
| Light | `font-light` | 300 |
| Regular | `font-normal` | 400 |
| Medium | `font-medium` | 500 |
| Semibold | `font-semibold` | 600 |
| Bold | `font-bold` | 700 |
| Extra Bold | `font-extrabold` | 800 |
| Black | `font-black` | 900 |

## Usage Examples

### Direct Tailwind Classes
```jsx
// Regular Noto Sans with different weights
<h1 className="font-noto-sans font-bold">Main Header</h1>
<p className="font-noto-sans font-normal">Body text</p>

// Condensed variants
<div className="font-noto-condensed font-medium">Compact Section</div>
<small className="font-noto-extra-condensed font-normal">Dense Info</small>
```

### Using the Font Utility Functions
```jsx
import { notoSans, notoSansPresets } from '@/utils/fonts';

// Programmatic font selection
<h2 className={notoSans('regular', 'semibold')}>Dynamic Header</h2>
<p className={notoSans('condensed', 'normal')}>Condensed Text</p>

// Predefined presets
<h1 className={notoSansPresets.h1}>Header 1</h1>
<button className={notoSansPresets.button}>Button</button>
<p className={notoSansPresets.body}>Body content</p>
```

## Predefined Presets

The font utility provides commonly used combinations:

- **Headers**: `h1`, `h2`, `h3`
- **Body Text**: `body`, `bodyBold`
- **UI Elements**: `button`, `label`, `caption`
- **Compact Layouts**: `compactHeader`, `compactBody`, `ultraCompact`

## CSS Variables

The following CSS variables are available for direct use:

```css
:root {
  --font-noto-sans: 'Noto Sans', system-ui, -apple-system, sans-serif;
  --font-noto-sans-condensed: 'Noto Sans Condensed', system-ui, -apple-system, sans-serif;
  --font-noto-sans-extra-condensed: 'Noto Sans Extra Condensed', system-ui, -apple-system, sans-serif;
}
```

## Performance Considerations

- **Variable Fonts**: Primary fonts use variable font technology for optimal file size
- **Static Fallbacks**: Static fonts are included for better browser compatibility  
- **Font Display**: All fonts use `font-display: swap` for improved loading performance
- **System Fallbacks**: Each font family includes system font fallbacks

## Browser Support

- **Variable Fonts**: Modern browsers (Chrome 62+, Firefox 62+, Safari 11+)
- **Static Fallbacks**: All browsers with TTF support
- **Progressive Enhancement**: Older browsers fall back to system fonts gracefully

## File Structure

```
public/fonts/Noto_Sans/
├── NotoSans-VariableFont_wdth,wght.ttf          # Variable font (regular)
├── NotoSans-Italic-VariableFont_wdth,wght.ttf   # Variable font (italic)
└── static/                                       # Static font files
    ├── NotoSans-Regular.ttf
    ├── NotoSans-Bold.ttf
    ├── NotoSans-Medium.ttf
    ├── NotoSans_Condensed-Regular.ttf
    ├── NotoSans_ExtraCondensed-Regular.ttf
    └── ... (additional weights and styles)
```

## Examples in Components

Check out the `TypographyDemo` component for live examples of all font variations and usage patterns.

```jsx
// Import and use the demo component
import TypographyDemo from '@/components/base/TypographyDemo';

<TypographyDemo />
```