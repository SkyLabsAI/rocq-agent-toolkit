import React from 'react';
import { notoSans, notoSansPresets, type NotoSansVariant, type NotoSansWeight } from '@/utils/fonts';

interface TypographyDemoProps {
  className?: string;
}

/**
 * Typography Demo Component
 * 
 * Demonstrates the usage of Noto Sans fonts with Tailwind CSS variables.
 * This component shows all available font variants and weights.
 */
export function TypographyDemo({ className = '' }: TypographyDemoProps) {
  return (
    <div className={`space-y-8 p-6 ${className}`}>
      <div>
        <h2 className="text-2xl font-bold mb-4">Noto Sans Typography Demo</h2>
        
        {/* Headers */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">Headers</h3>
          <h1 className={`text-4xl ${notoSansPresets.h1} mb-2`}>
            Main Heading (H1 - Bold)
          </h1>
          <h2 className={`text-3xl ${notoSansPresets.h2} mb-2`}>
            Section Heading (H2 - Semibold)
          </h2>
          <h3 className={`text-2xl ${notoSansPresets.h3} mb-2`}>
            Subsection Heading (H3 - Medium)
          </h3>
        </section>

        {/* Body Text */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">Body Text</h3>
          <p className={`${notoSansPresets.body} mb-4`}>
            This is regular body text using Noto Sans. It provides excellent readability 
            and supports a wide range of languages. The font is optimized for both 
            screen and print media.
          </p>
          <p className={`${notoSansPresets.bodyBold} mb-4`}>
            This is emphasized body text using medium weight for better hierarchy.
          </p>
        </section>

        {/* Font Variants */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">Font Variants</h3>
          <div className="space-y-2">
            <p className={notoSans('regular', 'normal')}>
              Regular Noto Sans - Perfect for body text and general content
            </p>
            <p className={notoSans('condensed', 'normal')}>
              Condensed Noto Sans - Great for space-constrained layouts
            </p>
            <p className={notoSans('extraCondensed', 'normal')}>
              Extra Condensed Noto Sans - Ultra-compact for dense information
            </p>
          </div>
        </section>

        {/* Weight Variations */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">Weight Variations</h3>
          <div className="space-y-2">
            <p className={notoSans('regular', 'light')}>Light (300)</p>
            <p className={notoSans('regular', 'normal')}>Regular (400)</p>
            <p className={notoSans('regular', 'medium')}>Medium (500)</p>
            <p className={notoSans('regular', 'semibold')}>Semibold (600)</p>
            <p className={notoSans('regular', 'bold')}>Bold (700)</p>
            <p className={notoSans('regular', 'extrabold')}>Extra Bold (800)</p>
            <p className={notoSans('regular', 'black')}>Black (900)</p>
          </div>
        </section>

        {/* UI Elements */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">UI Elements</h3>
          <div className="space-y-4">
            <button className={`${notoSansPresets.button} px-4 py-2 bg-blue-500 text-white rounded`}>
              Button Text
            </button>
            <div>
              <label className={`${notoSansPresets.label} block mb-1`}>
                Form Label
              </label>
              <input 
                type="text" 
                placeholder="Input field"
                className={`${notoSansPresets.body} px-3 py-2 border border-gray-300 rounded`}
              />
            </div>
            <p className={`${notoSansPresets.caption} text-gray-600 text-sm`}>
              Caption or helper text
            </p>
          </div>
        </section>

        {/* Compact Layouts */}
        <section className="mb-8">
          <h3 className="text-lg font-semibold mb-4">Compact Layouts</h3>
          <div className="bg-gray-100 p-4 rounded">
            <h4 className={`${notoSansPresets.compactHeader} mb-2`}>
              Compact Header
            </h4>
            <p className={`${notoSansPresets.compactBody} mb-2`}>
              Condensed body text for sidebar or card layouts where space is limited.
            </p>
            <p className={`${notoSansPresets.ultraCompact} text-sm`}>
              Ultra-compact text for dense information display, tables, or fine print.
            </p>
          </div>
        </section>
      </div>
    </div>
  );
}

export default TypographyDemo;