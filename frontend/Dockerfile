# Simple single-stage build for development
FROM node:22-alpine

# Set working directory
WORKDIR /app

# Copy all files
COPY . .

# Install pnpm
RUN npm install -g pnpm

# Install dependencies
RUN pnpm install

# Expose port 3005
EXPOSE 3005

ENV PORT=3005
ENV HOSTNAME="0.0.0.0"
ENV NODE_ENV="production"

# 1. Accept the build argument
ARG NEXT_PUBLIC_DATA_API
ENV NEXT_PUBLIC_DATA_API=${NEXT_PUBLIC_DATA_API}

# build project
RUN pnpm run build

# Start the application
CMD ["pnpm", "run", "start"]
