import { motion } from 'framer-motion';
import React, { useLayoutEffect, useRef, useState } from 'react';

export interface Tab {
  id: string;
  label: string;
  icon?: React.ReactNode;
}

export interface SlidingTabsProps {
  tabs: Tab[];
  defaultTab?: string;
  onTabChange?: (tabId: string) => void;
}

export const SlidingTabs: React.FC<SlidingTabsProps> = ({
  tabs,
  defaultTab,
  onTabChange,
}) => {
  const [activeTab, setActiveTab] = useState<string>(
    defaultTab || tabs[0]?.id || ''
  );
  const [slidePosition, setSlidePosition] = useState<{
    x: number;
    width: number;
    height: number;
  }>({ x: 0, width: 0, height: 0 });

  const buttonRefs = useRef<Record<string, HTMLButtonElement | null>>({});
  const containerRef = useRef<HTMLDivElement | null>(null);

  useLayoutEffect(() => {
    const updateSlidePosition = () => {
      const activeButton = buttonRefs.current[activeTab];
      const container = containerRef.current;

      if (activeButton && container) {
        const buttonRect = activeButton.getBoundingClientRect();
        const containerRect = container.getBoundingClientRect();

        setSlidePosition({
          x: buttonRect.left - containerRect.left,
          width: buttonRect.width,
          height: buttonRect.height,
        });
      }
    };

    // Update position on initial render and tab change
    updateSlidePosition();

    // Update position on window resize
    const handleResize = () => {
      updateSlidePosition();
    };

    window.addEventListener('resize', handleResize);

    return () => {
      window.removeEventListener('resize', handleResize);
    };
  }, [activeTab, tabs]);

  const handleTabClick = (tabId: string) => {
    if (tabId !== activeTab) {
      setActiveTab(tabId);
      onTabChange?.(tabId);
    }
  };

  if (!tabs || tabs.length === 0) {
    return null;
  }

  return (
    <div
      className={` relative rounded-sm w-fit p-[3px] border border-background-accent-gray-subtlest bg-elevation-surface-raised`}
    >
      <div ref={containerRef} className='flex gap-1 items-center relative'>
        {tabs.map(tab => (
          <button
            key={tab.id}
            ref={el => {
              buttonRefs.current[tab.id] = el;
            }}
            onClick={() => handleTabClick(tab.id)}
            className='flex gap-1 h-[30px] items-center justify-center px-2 py-[6.5px] relative rounded-[3px] cursor-pointer transition-colors z-10 focus:outline-none  focus:ring-opacity-50'
            type='button'
            role='tab'
            aria-selected={activeTab === tab.id}
            aria-controls={`tabpanel-${tab.id}`}
            id={`tab-${tab.id}`}
          >
            {tab.icon && (
              <span
                className={
                  activeTab === tab.id ? 'text-text' : 'text-text-disabled'
                }
              >
                {tab.icon}
              </span>
            )}
            <span
              className={`font-medium text-sm whitespace-nowrap transition-colors ${
                activeTab === tab.id ? 'text-text' : 'text-text-disabled'
              }`}
            >
              {tab.label}
            </span>
          </button>
        ))}

        <motion.div
          className={`absolute bg-background-accent-gray-subtlest pointer-events-none z-0 rounded-[3px]`}
          initial={false}
          animate={{
            x: slidePosition.x,
            width: slidePosition.width,
            height: slidePosition.height,
          }}
          transition={{
            type: 'spring',
            stiffness: 300,
            damping: 30,
          }}
        />
      </div>
    </div>
  );
};

export default SlidingTabs;
