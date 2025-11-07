
import { TaskStatus } from "@/types/types";
import cn from "classnames";

interface TaskButtonProps {
  status: TaskStatus;
}

const TaskButton: React.FC<TaskButtonProps> = ({ status }) => {
  return (
    <span
      className={cn(
        "inline-flex items-center px-2.5 py-1 rounded-full text-xs font-medium shadow-sm",
        status === "Success" 
          ? "bg-green-500/30 text-green-300 border border-green-400/50 shadow-green-500/20" 
          : "bg-red-500/30 text-red-300 border border-red-400/50 shadow-red-500/20"
      )}
    >
      {status === "Success" ? "✓ " : "✗ "}
      {status}
    </span>
  );
};
export default TaskButton;