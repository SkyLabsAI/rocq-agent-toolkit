import type { Metadata } from 'next';
export const metadata: Metadata = {
  title: 'RAT Dashboard',
};
import './globals.css';

import { Geist, Geist_Mono } from 'next/font/google';

import { SelectedRunProvider } from '@/contexts/SelectedRunContext';
import { ThemeProvider } from '@/contexts/ThemeContext';

const geistSans = Geist({
  variable: '--font-geist-sans',
  subsets: ['latin'],
});

const geistMono = Geist_Mono({
  variable: '--font-geist-mono',
  subsets: ['latin'],
});

const RootLayout = ({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) => {
  return (
    <html lang='en'>
      <body
        className={`${geistSans.variable} ${geistMono.variable} antialiased bg-elevation-surface text-text min-h-screen transition-colors`}
      >
        <ThemeProvider>
          <SelectedRunProvider>{children}</SelectedRunProvider>
        </ThemeProvider>
      </body>
    </html>
  );
};

export default RootLayout;
