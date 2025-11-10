import { useEffect, useState } from "react";
import { getData, refreshData } from "@/services/dataservice";
import { AgentSummary } from "@/types/types";

export const useAdminDashboard = () => {
  const [agentData, setAgentData] = useState<AgentSummary[]>([]);
  const [isRefreshing, setIsRefreshing] = useState(false);
  const [refreshMessage, setRefreshMessage] = useState<string>("");

  const fetchData = async () => {
    const data = await getData();
    setAgentData(data);
  };

  useEffect(() => {
    fetchData();
  }, []);

  const handleRefresh = async () => {
    setIsRefreshing(true);
    setRefreshMessage("");
    try {
      const result = await refreshData();
      if (result.success) {
        setRefreshMessage(result.message);
        await fetchData();
        // Clear message after 3 seconds
        setTimeout(() => setRefreshMessage(""), 3000);
      }
    } catch (error) {
      console.error("Error refreshing data:", error);
      setRefreshMessage("Error refreshing data. Please try again.");
      setTimeout(() => setRefreshMessage(""), 3000);
    } finally {
      setIsRefreshing(false);
    }
  };

  return {
    agentData,
    isRefreshing,
    refreshMessage,
    handleRefresh,
  };
};