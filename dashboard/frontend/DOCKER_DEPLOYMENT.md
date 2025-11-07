# Docker Deployment Guide

## Quick Start

### Using Docker Compose (Recommended)

1. **Build and run the container:**
   ```bash
   docker-compose up -d --build
   ```

2. **Access the dashboard:**
   - Open your browser and go to `http://localhost:8080`
   - Admin dashboard: `http://localhost:8080/admin`
   - Compare view: `http://localhost:8080/admin/compare`

3. **View logs:**
   ```bash
   docker-compose logs -f rat-public-dashboard
   ```

4. **Stop the container:**
   ```bash
   docker-compose down
   ```

### Using Docker directly

1. **Build the image:**
   ```bash
   docker build -t rat-public-dashboard .
   ```

2. **Run the container:**
   ```bash
   docker run -d -p 8080:80 --name rat-public-dashboard rat-public-dashboard
   ```

3. **Stop the container:**
   ```bash
   docker stop rat-public-dashboard
   docker rm rat-public-dashboard
   ```

## Configuration

### Changing the Port

To run on a different port, modify the port mapping in `docker-compose.yml`:

```yaml
ports:
  - "3000:80"  # This will serve on port 3000
```

Or with Docker directly:
```bash
docker run -d -p 3000:80 --name rat-public-dashboard rat-public-dashboard
```

### Custom Domain

Update the `server_name` in `nginx.conf`:

```nginx
server {
    listen 80;
    server_name yourdomain.com;
    # ... rest of config
}
```

### HTTPS/SSL

For production with HTTPS, you can:

1. Use a reverse proxy like Traefik or Caddy
2. Add SSL certificates to the nginx configuration
3. Use a cloud service with built-in SSL termination

## Troubleshooting

### Container won't start
```bash
docker logs rat-public-dashboard
```

### Build issues
```bash
docker-compose build --no-cache
```

### Check if container is running
```bash
docker ps
```

### Access container shell
```bash
docker exec -it rat-public-dashboard /bin/sh
```

## Production Deployment

For production deployment on a self-hosted server:

1. **Clone the repository on your server**
2. **Set up environment variables as needed**
3. **Run with docker-compose:**
   ```bash
   docker-compose -f docker-compose.yml up -d --build
   ```

4. **Set up a reverse proxy (optional but recommended):**
   - Use nginx or Apache as a reverse proxy
   - Configure SSL certificates
   - Set up domain routing

## Resource Requirements

- **RAM:** 512MB minimum, 1GB recommended
- **CPU:** 1 core minimum
- **Disk:** 100MB for the container + your data
- **Network:** Standard HTTP/HTTPS ports (80/443)