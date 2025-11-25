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

# build project
RUN pnpm run build

# Start the application
CMD ["pnpm", "run", "start"]
