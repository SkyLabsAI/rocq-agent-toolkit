export function StatusBadge({ status }: { status: string }) {
  const isSuccess = status.toLowerCase() === 'success';
  return (
    <div className='inline-flex items-center'>
      <div
        className={`h-5 rounded-[15px] px-3 py-0.5 ${isSuccess ? 'bg-background-success opacity-50' : 'bg-background-danger'}`}
      >
        <p
          className={`font-inter font-semibold text-xs ${isSuccess ? 'text-text-success' : 'text-text-danger'}`}
        >
          {status}
        </p>
      </div>
    </div>
  );
}