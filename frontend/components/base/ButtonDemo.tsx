import React, { useState } from 'react';
import Button from './Button';

/**
 * Button Demo Component
 * 
 * Demonstrates all variants and usage patterns of the base Button component.
 */
export function ButtonDemo() {
  const [loading, setLoading] = useState<string | null>(null);

  const handleAsyncAction = (buttonId: string) => {
    setLoading(buttonId);
    setTimeout(() => setLoading(null), 2000);
  };

  // Example icons
  const RefreshIcon = (
    <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
    </svg>
  );

  const PlusIcon = (
    <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
    </svg>
  );

  const ArrowIcon = (
    <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5l7 7-7 7" />
    </svg>
  );

  return (
    <div className="space-y-8 p-6 bg-gray-900 min-h-screen">
      <div>
        <h1 className="text-3xl font-bold text-white mb-2">Button Component Demo</h1>
        <p className="text-gray-400">
          Showcasing all variants, sizes, and usage patterns of the base Button component.
        </p>
      </div>

      {/* Variants */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Variants</h2>
        <div className="flex flex-wrap gap-4">
          <Button variant="primary">Primary</Button>
          <Button variant="secondary">Secondary</Button>
          <Button variant="outline">Outline</Button>
          <Button variant="ghost">Ghost</Button>
          <Button variant="danger">Danger</Button>
          <Button variant="success">Success</Button>
        </div>
      </section>

      {/* Sizes */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Sizes</h2>
        <div className="flex flex-wrap items-center gap-4">
          <Button size="sm">Small</Button>
          <Button size="md">Medium</Button>
          <Button size="lg">Large</Button>
          <Button size="xl">Extra Large</Button>
        </div>
      </section>

      {/* With Icons */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">With Icons</h2>
        <div className="flex flex-wrap gap-4">
          <Button leftIcon={PlusIcon}>Add Item</Button>
          <Button rightIcon={ArrowIcon} variant="outline">Continue</Button>
          <Button leftIcon={RefreshIcon} rightIcon={ArrowIcon} variant="secondary">
            Refresh & Next
          </Button>
        </div>
      </section>

      {/* Loading States */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Loading States</h2>
        <div className="flex flex-wrap gap-4">
          <Button 
            loading={loading === 'async1'} 
            onClick={() => handleAsyncAction('async1')}
          >
            {loading === 'async1' ? 'Processing...' : 'Process Data'}
          </Button>
          <Button 
            variant="success"
            loading={loading === 'async2'} 
            onClick={() => handleAsyncAction('async2')}
            leftIcon={!loading ? RefreshIcon : undefined}
          >
            {loading === 'async2' ? 'Refreshing...' : 'Refresh'}
          </Button>
        </div>
      </section>

      {/* Disabled States */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Disabled States</h2>
        <div className="flex flex-wrap gap-4">
          <Button disabled>Disabled Button</Button>
          <Button disabled variant="danger" leftIcon={PlusIcon}>
            Disabled with Icon
          </Button>
        </div>
      </section>

      {/* Custom Styling */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Custom Styling</h2>
        <div className="flex flex-wrap gap-4">
          <Button 
            variant="primary" 
            className="bg-purple-500/20 hover:bg-purple-500/30 border-purple-400/30 text-purple-400"
          >
            Custom Purple
          </Button>
          <Button 
            variant="outline" 
            className="rounded-full px-8"
          >
            Fully Rounded
          </Button>
          <Button 
            variant="ghost" 
            className="border border-dashed border-gray-500 hover:border-white"
          >
            Dashed Border
          </Button>
        </div>
      </section>

      {/* Real-world Examples */}
      <section className="space-y-4">
        <h2 className="text-xl font-semibold text-white">Real-world Examples</h2>
        <div className="space-y-4">
          {/* Form Actions */}
          <div className="bg-white/5 border border-white/10 rounded-lg p-4">
            <h3 className="text-lg font-medium text-white mb-3">Form Actions</h3>
            <div className="flex gap-3">
              <Button variant="primary" size="sm">Save</Button>
              <Button variant="outline" size="sm">Cancel</Button>
              <Button variant="ghost" size="sm">Reset</Button>
            </div>
          </div>

          {/* Data Table Actions */}
          <div className="bg-white/5 border border-white/10 rounded-lg p-4">
            <h3 className="text-lg font-medium text-white mb-3">Data Table Actions</h3>
            <div className="flex gap-3">
              <Button variant="primary" leftIcon={PlusIcon} size="sm">
                Add New
              </Button>
              <Button variant="outline" leftIcon={RefreshIcon} size="sm">
                Refresh
              </Button>
              <Button variant="danger" size="sm">
                Delete Selected
              </Button>
            </div>
          </div>

          {/* Navigation */}
          <div className="bg-white/5 border border-white/10 rounded-lg p-4">
            <h3 className="text-lg font-medium text-white mb-3">Navigation</h3>
            <div className="flex gap-3">
              <Button variant="ghost" size="sm">← Previous</Button>
              <Button variant="primary" size="sm">Next →</Button>
            </div>
          </div>
        </div>
      </section>
    </div>
  );
}

export default ButtonDemo;