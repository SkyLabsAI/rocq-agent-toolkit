'use client';

import React, { Suspense } from 'react';
import type { TaskOutput, RunDetailsResponse } from '@/types/types';

export interface RunStats {
  id: string;
  name: string;
  tasks: number;
  successRate: number;
  totalLlmCalls: number;
  totalTokens: number;
  avgExecutionTime: number;
}

export interface RunTaskCell {
  run: RunDetailsResponse;
  task?: TaskOutput;
}

const ComparePage: React.FC = () => {
  return (
    <Layout title='Compare Runs'>
      <div className='  text-white p-8'>
        <div className='max-w-7xl mx-auto space-y-8'></div>
        <Suspense
          fallback={
            <div className='min-h-screen  text-white p-8'>
              <div className='max-w-7xl mx-auto'>
                <div className='flex items-center justify-center h-64'>
                  <div className='text-gray-400'>
                    Loading comparison data...
                  </div>
                </div>
              </div>
            </div>
          }
        >
          <ComparePageContent />
        </Suspense>
      </div>
    </Layout>
  );
};

export default ComparePage;

// We trying something else

import { StatusBadge } from '@/components/base/statusBadge';
import { ComparePageContent } from './compare-page-content';
import Layout from '@/layouts/common';

// SVG Paths Data
const svgPaths = {
  p19cba180:
    'M5.5575 11.5575L9 8.1225L12.4425 11.5575L13.5 10.5L9 6L4.5 10.5L5.5575 11.5575Z',
  p22a90b00:
    'M13.5 15.75L10.5 12.75H12.75V5.25H10.5L13.5 2.25L16.5 5.25H14.25V12.75H16.5M1.5 14.25V12.75H9V14.25M1.5 9.75V8.25H6.75V9.75M1.5 5.25V3.75H4.5V5.25H1.5Z',
  p2ee6540:
    'M2.13441 8.5377C4.41249 10.9547 7.17594 13.9978 10.4052 13.7858C13.1812 13.6035 15.1018 11.0425 14.938 7.69709C14.787 4.6141 12.5025 2.06597 9.66982 2.25197C6.38394 2.4677 4.22821 6.03118 2.13441 8.5377ZM18.4963 7.2755C18.5004 7.33778 18.504 7.40021 18.5071 7.46275C18.7834 13.1041 15.5833 17.3942 10.8245 17.7067C6.23563 18.0079 3.05311 14.5316 0 11.3759L6.55634 2.64432C7.73688 1.12438 9.21573 0.299883 10.727 0.0684127C10.9638 0.0403434 11.2032 0.0182339 11.4454 0.00278286C14.8441 -0.100849 18.1949 2.70281 18.4963 7.2755Z',
  p3053c630: 'M7.41 15.41L12 10.83L16.59 15.41L18 14L12 8L6 14L7.41 15.41Z',
  p3d55a600:
    'M0 0.0851374C0.0311687 0.0833715 0.0619562 0.0807228 0.0930296 0.0787362C0.332625 0.0714154 0.572412 0.0497104 0.811435 0.0131061C0.848418 0.00872833 0.885624 0.00471842 0.92248 9.53674e-06C0.328971 0.0909131 0 0.0851374 0 0.0851374Z',
  pa717500: 'M8 5.14V19.14L19 12.14L8 5.14Z',
  pa7e5b00:
    'M0.00257357 6.08608C0.00257357 6.08608 4.33475 0.816181 10.7579 0C8.98442 0.271643 4.84797 1.40718 0.0607807 6.14428L0 6.22256V6.08343C0.000857856 6.08431 0.00171571 6.08519 0.00257357 6.08608Z',
  pbb00e00:
    'M16.3893 9.1873C14.1112 6.77032 11.3478 3.72721 8.11853 3.93922C5.34254 4.12147 3.4219 6.68247 3.58571 10.0279C3.7367 13.1109 6.02123 15.659 8.85387 15.473C12.1397 15.2573 14.2955 11.6938 16.3893 9.1873ZM0.0273588 10.4495C0.0232601 10.3872 0.0196702 10.3248 0.0165882 10.2622C-0.259673 4.6209 2.94035 0.330783 7.69917 0.0183414C12.2881 -0.282916 15.4706 3.19338 18.5237 6.34906L11.9674 15.0807C10.7868 16.6006 9.30797 17.4251 7.79668 17.6566C7.55994 17.6847 7.3205 17.7068 7.07827 17.7222C3.67957 17.8258 0.328816 15.0222 0.0273588 10.4495Z',
  pd8f5f00:
    'M0.92248 7.46715e-05C0.891311 0.0018405 0.860524 0.00448925 0.82945 0.00647582C0.589855 0.0137967 0.350068 0.0354649 0.111045 0.0721059C0.0740615 0.0764837 0.036856 0.0804936 0 0.0852025C0.593508 -0.00573787 0.92248 7.46715e-05 0.92248 7.46715e-05Z',
  pfcfcf00:
    'M10.7553 0.136485C10.7553 0.136485 6.42312 5.40638 0 6.22256C1.77344 5.95092 5.9099 4.81538 10.6971 0.0782866L10.7579 1.49864e-06V0.139134C10.757 0.138251 10.7562 0.137368 10.7553 0.136485Z',
};

// Image Data
const imgG22 =
  'data:image/svg+xml,%3Csvg%20preserveAspectRatio%3D%22none%22%20width%3D%22100%25%22%20height%3D%22100%25%22%20overflow%3D%22visible%22%20style%3D%22display%3A%20block%3B%22%20viewBox%3D%220%200%2064%2074%22%20fill%3D%22none%22%20xmlns%3D%22http%3A%2F%2Fwww.w3.org%2F2000%2Fsvg%22%3E%0A%3Cg%20id%3D%22clipPath20%22%3E%0A%3Cpath%20id%3D%22path18%22%20d%3D%22M0.00012207%2073.5762H63.545V0H0.00012207V73.5762Z%22%20fill%3D%22var(--fill-0%2C%20black)%22%2F%3E%0A%3C%2Fg%3E%0A%3C%2Fsvg%3E%0A';

// Logo Components
const LogoG1 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-21.243px_-21.569px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g22'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <svg
      className='block size-full'
      fill='none'
      preserveAspectRatio='none'
      viewBox='0 0 11 7'
    >
      <g id='g22'>
        <path d={svgPaths.pfcfcf00} fill='var(--fill-0, #669DF1)' id='path24' />
      </g>
    </svg>
  </div>
);

const LogoG2 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-20.321px_-21.484px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g26'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <div className=' bottom-[-0.01%] left-0 right-0 top-0'>
      <svg
        className='block size-full'
        fill='none'
        preserveAspectRatio='none'
        viewBox='0 0 1 1'
      >
        <g id='g26'>
          <path
            d={svgPaths.p3d55a600}
            fill='var(--fill-0, #669DF1)'
            id='path28'
          />
        </g>
      </svg>
    </div>
  </div>
);

const LogoG3 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-13.336px_-21.488px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g30'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <svg
      className='block size-full'
      fill='none'
      preserveAspectRatio='none'
      viewBox='0 0 19 18'
    >
      <g id='g30'>
        <path d={svgPaths.pbb00e00} fill='var(--fill-0, #669DF1)' id='path32' />
      </g>
    </svg>
  </div>
);

const LogoG4 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-31.67px_-32.634px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g34'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <svg
      className='block size-full'
      fill='none'
      preserveAspectRatio='none'
      viewBox='0 0 11 7'
    >
      <g id='g34'>
        <path d={svgPaths.pa7e5b00} fill='var(--fill-0, #669DF1)' id='path36' />
      </g>
    </svg>
  </div>
);

const LogoG5 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-42.429px_-38.856px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g38'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <div className=' bottom-0 left-0 right-0 top-[-0.01%]'>
      <svg
        className='block size-full'
        fill='none'
        preserveAspectRatio='none'
        viewBox='0 0 1 1'
      >
        <g id='g38'>
          <path
            d={svgPaths.pd8f5f00}
            fill='var(--fill-0, #669DF1)'
            id='path40'
          />
        </g>
      </svg>
    </div>
  </div>
);

const LogoG6 = () => (
  <div
    className='mask-alpha mask-intersect mask-no-clip mask-no-repeat mask-position-[-31.813px_-21.213px] mask-size-[63.545px_73.576px] relative size-full'
    data-name='g42'
    style={{ maskImage: `url('${imgG22}')` }}
  >
    <svg
      className='block size-full'
      fill='none'
      preserveAspectRatio='none'
      viewBox='0 0 19 18'
    >
      <g id='g42'>
        <path d={svgPaths.p2ee6540} fill='var(--fill-0, #669DF1)' id='path44' />
      </g>
    </svg>
  </div>
);

const Logo = () => (
  <div className=' contents inset-0' data-name='g16'>
    <div className=' flex inset-[1.98%_49.55%_63.45%_21.37%] items-center justify-center'>
      <div className='flex-none h-[6.223px] scale-y-[-100%] w-[10.758px]'>
        <LogoG1 />
      </div>
    </div>
    <div className=' flex inset-[1.51%_78.63%_98.02%_18.88%] items-center justify-center'>
      <div className='flex-none h-[0.085px] scale-y-[-100%] w-[0.922px]'>
        <LogoG2 />
      </div>
    </div>
    <div className=' bottom-0 flex items-center justify-center left-0 right-[49.94%] top-[1.53%]'>
      <div className='flex-none h-[17.725px] scale-y-[-100%] w-[18.524px]'>
        <LogoG3 />
      </div>
    </div>
    <div className=' flex inset-[63.45%_21.37%_1.98%_49.55%] items-center justify-center'>
      <div className='flex-none h-[6.223px] scale-y-[-100%] w-[10.758px]'>
        <LogoG4 />
      </div>
    </div>
    <div className=' flex inset-[98.02%_18.88%_1.51%_78.63%] items-center justify-center'>
      <div className='flex-none h-[0.085px] scale-y-[-100%] w-[0.922px]'>
        <LogoG5 />
      </div>
    </div>
    <div className=' bottom-[1.53%] flex items-center justify-center left-[49.94%] right-0 top-0'>
      <div className='flex-none h-[17.725px] scale-y-[-100%] w-[18.524px]'>
        <LogoG6 />
      </div>
    </div>
  </div>
);

const Icon = () => (
  <div
    className=' h-[18px] left-[40px] overflow-clip top-[15px] w-[37px]'
    data-name='icon (1) 1'
  >
    <Logo />
  </div>
);

// Header Components
const HeaderBar = () => (
  <div className=' bg-[#1d1e20] h-[48px] left-0 top-0 w-[1280px]'>
    <div className='h-[48px] overflow-clip relative rounded-[inherit] w-[1280px]'>
      <p
        className=" font-['Noto_Sans:Regular',sans-serif] font-normal leading-[normal] left-[88px] text-[#cecfd2] text-[16px] text-nowrap top-[13px] whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Skylabs AI
      </p>
      <p
        className=" font-['Noto_Sans:Regular',sans-serif] font-normal leading-[normal] left-[200px] text-[#96999e] text-[16px] text-nowrap top-[13px] whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Internal Dashboard
      </p>
      <Icon />
      <div
        className=' flex h-[calc(1px*((var(--transform-inner-width)*1)+(var(--transform-inner-height)*0)))] items-center justify-center left-[182px] top-[10px] w-[calc(1px*((var(--transform-inner-height)*1)+(var(--transform-inner-width)*0)))]'
        style={
          {
            '--transform-inner-width': '27',
            '--transform-inner-height': '0',
          } as React.CSSProperties
        }
      >
        <div className='flex-none rotate-[90deg]'>
          <div className='h-0 relative w-[27px]'>
            <div
              className=' bottom-0 left-0 right-0 top-[-1px]'
              style={
                { '--stroke-0': 'rgba(57, 61, 70, 1)' } as React.CSSProperties
              }
            >
              <svg
                className='block size-full'
                fill='none'
                preserveAspectRatio='none'
                viewBox='0 0 27 1'
              >
                <line
                  id='Line 9'
                  stroke='var(--stroke-0, #393D46)'
                  x2='27'
                  y1='0.5'
                  y2='0.5'
                />
              </svg>
            </div>
          </div>
        </div>
      </div>
    </div>
    <div
      aria-hidden='true'
      className=' border-[#2b2c2f] border-[0px_0px_1px] border-solid inset-0 pointer-events-none'
    />
  </div>
);

// const RunsSection = () => (
//   <div className=' h-[207px] left-0 overflow-clip top-[128px] w-[1280px]'>
//     <RunsHeader />
//     <RunRow />
//     <RunRow2 />
//   </div>
// );

// Comparison Section Components
const ComparisonHeaderBar = () => (
  <div className=' bg-[#1d1e20] box-border content-stretch flex items-center justify-between left-[40px] overflow-clip px-[24px] py-[16px] rounded-[4px] top-[336px] w-[1200px]'>
    <div className='basis-0 content-stretch flex grow items-center justify-between min-h-px min-w-px relative shrink-0'>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Taskwise Comparison
      </p>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Run_RocqAgent_001
      </p>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Run_RocqAgent_002
      </p>
      {/* <FilterFieldsButton /> */}
    </div>
  </div>
);

