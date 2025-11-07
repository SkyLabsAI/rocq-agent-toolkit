// Configuration for the frontend application
// You can set NEXT_PUBLIC_DATA_API environment variable to override the default

export const config = {
    DATA_API: process.env.NEXT_PUBLIC_DATA_API || 'http://localhost:8000/api',
}

