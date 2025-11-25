// Configuration for the frontend application
// You can set NEXT_PUBLIC_DATA_API environment variable to override the default
// Set NEXT_PUBLIC_USE_MOCK_DATA=true to use mock data instead of real API calls

export const config = {
    DATA_API: process.env.NEXT_PUBLIC_DATA_API || 'http://localhost:8000/api',
    USE_MOCK_DATA: process.env.NEXT_PUBLIC_USE_MOCK_DATA === 'true',
}

