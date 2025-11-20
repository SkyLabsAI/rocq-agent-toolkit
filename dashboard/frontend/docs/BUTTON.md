# Button Component

A reusable, accessible button component with consistent styling and multiple variants. Built with Tailwind CSS and designed to be easily customizable while maintaining design system consistency.

## Features

- **Multiple Variants**: Primary, secondary, outline, ghost, danger, success
- **Flexible Sizing**: Small, medium, large, extra large
- **Icon Support**: Left and right icon placement
- **Loading States**: Built-in loading spinner with automatic icon replacement
- **Accessibility**: Full keyboard navigation and screen reader support
- **Customizable**: Override styles via className prop
- **TypeScript**: Full type safety with comprehensive prop definitions

## Basic Usage

```tsx
import { Button } from '@/components/base';

// Simple button
<Button>Click me</Button>

// With variant and size
<Button variant="primary" size="lg">Primary Button</Button>

// With icons
<Button leftIcon={<PlusIcon />} variant="success">
  Add Item
</Button>
```

## Props

| Prop | Type | Default | Description |
|------|------|---------|-------------|
| `variant` | `'primary' \| 'secondary' \| 'outline' \| 'ghost' \| 'danger' \| 'success'` | `'primary'` | Visual style variant |
| `size` | `'sm' \| 'md' \| 'lg' \| 'xl'` | `'md'` | Button size |
| `loading` | `boolean` | `false` | Shows loading spinner and disables button |
| `leftIcon` | `React.ReactNode` | - | Icon displayed before text |
| `rightIcon` | `React.ReactNode` | - | Icon displayed after text |
| `className` | `string` | - | Additional CSS classes |
| `children` | `React.ReactNode` | - | Button content |
| `disabled` | `boolean` | `false` | Disables the button |
| `onClick` | `(event: MouseEvent) => void` | - | Click handler |

All standard HTML button attributes are also supported.

## Variants

### Primary
Default variant with blue styling. Use for main actions.
```tsx
<Button variant="primary">Save Changes</Button>
```

### Secondary  
Neutral gray styling. Use for secondary actions.
```tsx
<Button variant="secondary">Cancel</Button>
```

### Outline
Transparent background with border. Use for alternative actions.
```tsx
<Button variant="outline">Learn More</Button>
```

### Ghost
Minimal styling with no border. Use for subtle actions.
```tsx
<Button variant="ghost">Skip</Button>
```

### Danger
Red styling for destructive actions.
```tsx
<Button variant="danger">Delete</Button>
```

### Success
Green styling for positive actions.
```tsx
<Button variant="success">Confirm</Button>
```

## Sizes

```tsx
<Button size="sm">Small</Button>
<Button size="md">Medium (default)</Button>
<Button size="lg">Large</Button>
<Button size="xl">Extra Large</Button>
```

## With Icons

```tsx
// Left icon
<Button leftIcon={<RefreshIcon />}>
  Refresh Data
</Button>

// Right icon
<Button rightIcon={<ArrowIcon />}>
  Continue
</Button>

// Both icons
<Button leftIcon={<SaveIcon />} rightIcon={<ArrowIcon />}>
  Save & Next
</Button>
```

## Loading State

```tsx
const [loading, setLoading] = useState(false);

<Button 
  loading={loading}
  onClick={async () => {
    setLoading(true);
    await saveData();
    setLoading(false);
  }}
>
  {loading ? 'Saving...' : 'Save'}
</Button>
```

## Custom Styling

Override default styles using the `className` prop:

```tsx
// Custom colors
<Button 
  variant="primary"
  className="bg-purple-500/20 hover:bg-purple-500/30 border-purple-400/30 text-purple-400"
>
  Custom Purple
</Button>

// Custom shape
<Button 
  variant="outline"
  className="rounded-full px-8"
>
  Fully Rounded
</Button>

// Custom border
<Button 
  variant="ghost"
  className="border border-dashed border-gray-500"
>
  Dashed Border
</Button>
```

## Common Patterns

### Form Actions
```tsx
<div className="flex gap-3">
  <Button variant="primary" size="sm">Save</Button>
  <Button variant="outline" size="sm">Cancel</Button>
  <Button variant="ghost" size="sm">Reset</Button>
</div>
```

### Data Table Actions
```tsx
<div className="flex gap-3">
  <Button variant="primary" leftIcon={<PlusIcon />} size="sm">
    Add New
  </Button>
  <Button variant="outline" leftIcon={<RefreshIcon />} size="sm">
    Refresh
  </Button>
  <Button variant="danger" size="sm">
    Delete Selected
  </Button>
</div>
```

### Navigation
```tsx
<div className="flex gap-3">
  <Button variant="ghost" size="sm">← Previous</Button>
  <Button variant="primary" size="sm">Next →</Button>
</div>
```

## Accessibility

- Uses semantic `<button>` element
- Proper focus management with visible focus rings
- Screen reader compatible
- Keyboard navigation support
- Disabled state properly communicated to assistive technologies

## Design Tokens

The button component uses consistent design tokens:

- **Border Radius**: `rounded-lg` (8px)
- **Border Width**: `border` (1px)  
- **Font Weight**: `font-medium` (500)
- **Transition**: `transition-all duration-200`
- **Focus Ring**: `focus:ring-2 focus:ring-blue-500/50`

## Demo

See `ButtonDemo.tsx` for a comprehensive showcase of all button variants and usage patterns.