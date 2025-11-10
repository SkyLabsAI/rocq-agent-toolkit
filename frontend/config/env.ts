// Configuration for the frontend application
// You can set NEXT_PUBLIC_DATA_API environment variable to override the default

export const config = {
    DATA_API: process.env.NEXT_PUBLIC_DATA_API || 'http://192.168.68.54:8000/api',
}

