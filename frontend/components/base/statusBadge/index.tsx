export function StatusBadge({ status }: { status: string }) {
  const lowerStatus = status.toLowerCase();
  const isSuccess = lowerStatus === 'success';
  const isNotFound = lowerStatus === 'not found';
  return (
    <div className='flex items-center'>
      <div
        className={`h-5 rounded-[15px] px-3 py-0.5 ${
          isSuccess
            ? 'bg-background-success/50'
            : isNotFound
            ? 'bg-gray-300'
            : 'bg-background-danger'
        }`}
      >
        <p
          className={`font-inter font-semibold text-xs ${
            isSuccess
              ? 'text-text-success'
              : isNotFound
              ? 'text-gray-600'
              : 'text-text-danger'
          }`}
        >
          {status}
        </p>
      </div>
    </div>
  );
}