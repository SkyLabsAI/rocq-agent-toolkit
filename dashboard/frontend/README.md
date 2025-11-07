## RAT Public Dashboard

This directory contains the public dashboard UI built with **Next.js (App Router)** and **TypeScript**. It was copied into this mono-repo and is now managed by the main repository (not as a submodule).

### 1. Prerequisites

Install / have:

1. Node.js (recommend 18.x LTS or newer) – check:
```bash
node -v
```
2. Install pnpm globally (preferred package manager):
```bash
npm install -g pnpm
```

Optional checks:
```bash
pnpm -v
```

### 2. Install Dependencies

From the repository root or inside this folder:
```bash
cd rat-public-dashboard
pnpm install
```
This will read `pnpm-lock.yaml` and install exact versions.

### 3. Run the Development Server

```bash
pnpm run dev
```

Then open:
```
http://localhost:3000
```

Hot reload is enabled. Edit `app/page.tsx` or any component under `app/` or `components/` and the browser will refresh automatically.

### 4. Common Scripts

```bash
pnpm run dev      # start local dev server
pnpm run build    # production build
pnpm start        # run built app
pnpm lint         # run ESLint
```

### 5. Environment Variables (If Needed)

If this project later requires runtime configuration, create a `.env.local` file in this folder. Example:
```env
NEXT_PUBLIC_API_BASE_URL=http://localhost:8000
```
Never commit secrets; `.env.local` should be gitignored.

### 6. Updating Dependencies

```bash
pnpm add <package>
pnpm remove <package>
```

### 7. Troubleshooting

- If you see module resolution errors: delete `node_modules` and run `pnpm install` again.
- If pnpm complains about store corruption: `pnpm store prune`.
- If port 3000 is busy: `pnpm run dev -- --port=3001`.

### 8. Learn More (Optional Links)

- Next.js Docs: https://nextjs.org/docs
- App Router Basics: https://nextjs.org/docs/app/building-your-application/routing
- pnpm Docs: https://pnpm.io

### 9. Production Build & Run

```bash
pnpm run build
pnpm start
```
This serves the built output (defaults to port 3000 unless changed).

---
Maintained as part of the main repository. Update this README if setup steps change.
