'use client';

import { useRouter } from 'next/navigation';
import { use, useEffect } from 'react';

const ProjectPage = ({ params }: { params: Promise<{ id: string }> }) => {
  const { id } = use(params);
  const router = useRouter();

  useEffect(() => {
    if (id) {
      // Redirect old /project/[id] routes to /taskset?id=...
      router.replace(`/taskset?id=${encodeURIComponent(id)}`);
    }
  }, [id, router]);

  if (!id) {
    return <div>No taskset ID provided</div>;
  }

  return <div>Redirecting...</div>;
};

export default ProjectPage;
