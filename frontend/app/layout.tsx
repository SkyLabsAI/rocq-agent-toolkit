import type { Metadata } from 'next';
export const metadata: Metadata = {
  title: 'RAT Dashboard',
};
import { Geist, Geist_Mono } from 'next/font/google';
import { ThemeProvider } from '@/contexts/ThemeContext';
import './globals.css';
import { SelectedRunProvider } from '@/contexts/SelectedRunContext';

const geistSans = Geist({
  variable: '--font-geist-sans',
  subsets: ['latin'],
});

const geistMono = Geist_Mono({
  variable: '--font-geist-mono',
  subsets: ['latin'],
});

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
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
}
