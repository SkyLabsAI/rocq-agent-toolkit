// Environment configuration
// Next.js automatically loads .env files, but we can use dotenv for additional control
import dotenv from 'dotenv';

// Load environment variables from .env file (useful for server-side or build-time variables)
if (typeof window === 'undefined') {
  // Only load dotenv on server-side
  dotenv.config();
}

export const config = {
  DATA_API: process.env.NEXT_PUBLIC_DATA_API || 'http://localhost:8000/api',
  NODE_ENV: process.env.NODE_ENV || 'development',
  USE_MOCK_DATA: process.env.NEXT_PUBLIC_USE_MOCK_DATA === 'true',
  // Add more environment variables as needed
} as const;
