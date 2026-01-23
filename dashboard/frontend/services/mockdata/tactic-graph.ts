import { type TacticGraphResponse } from '@/services/dataservice';

export const getTacticGraphMock = async (
  runId: string,
  taskId: number
): Promise<TacticGraphResponse> => {
  // Simulate network delay
  await new Promise(resolve => setTimeout(resolve, 300));

  // Create a large graph with lots of nodes and repeating edges
  const nodeCount = 12;
  const nodes = [];
  const edges = [];

  // Generate nodes
  for (let i = 0; i < nodeCount; i++) {
    const hasError = i % 5 === 0; // Some nodes have errors
    nodes.push({
      id: `node_${i.toString(16).padStart(8, '0')}`,
      index: i + 1,
      information: {
        result: hasError
          ? `JsonRPCTP.Err(message="Tactic failed: strategy exhausted", data=CommandError(feedback_messages=[], error_loc=RocqLoc(...)))`
          : `JsonRPCTP.Ok(proof_state={focused_goals: ["Goal ${i}: ∀ n : nat, n + 0 = n"], unfocused_goals: [], shelved_goals: 0, given_up_goals: 0})`,
        error: hasError,
        proof_state: hasError
          ? undefined
          : {
              focused_goals: [`Goal ${i}: ∀ n : nat, n + 0 = n`],
              unfocused_goals: [],
              shelved_goals: 0,
              given_up_goals: 0,
            },
      },
    });
  }

  // Generate edges with various patterns

  let edgeIndex = 1; // Track edge index

  // 1. Sequential edges (main flow)
  for (let i = 0; i < nodeCount - 1; i++) {
    const hasTacticError = i === 3 || i === 7; // Some tactics fail
    edges.push({
      source: `node_${i.toString(16).padStart(8, '0')}`,
      target: `node_${(i + 1).toString(16).padStart(8, '0')}`,
      label: hasTacticError
        ? `failed_tactic_${i + 1}`
        : `progress tactic_${i + 1}`,
      index: edgeIndex++,
      information: {
        result: hasTacticError
          ? `JsonRPCTP.Err(message="Tactic application failed")`
          : `Applied tactic successfully`,
        error: hasTacticError,
      },
    });
  }

  // 2. Self-loops (multiple on some nodes)
  // Node 2 has 3 self-loops
  for (let i = 0; i < 3; i++) {
    edges.push({
      source: 'node_00000002',
      target: 'node_00000002',
      label:
        i === 1
          ? `try_tactic_variant_${i + 1}_with_extended_parameters_including_hints_from_databases_and_specific_unification_strategies_for_complex_pattern_matching_scenarios`
          : `try tactic_variant_${i + 1}`,
      index: edgeIndex++,
      information: {
        result: `Attempting alternative approach ${i + 1}`,
        error: false,
      },
    });
  }

  // Node 5 has 2 self-loops
  for (let i = 0; i < 2; i++) {
    edges.push({
      source: 'node_00000005',
      target: 'node_00000005',
      label: `refine ${i + 1}`,
      index: edgeIndex++,
      information: {
        result: `Refining proof ${i + 1}`,
        error: false,
      },
    });
  }

  // Node 8 has 4 self-loops (some with errors)
  for (let i = 0; i < 4; i++) {
    const hasError = i % 2 === 1;
    edges.push({
      source: 'node_00000008',
      target: 'node_00000008',
      label: hasError ? `failed_tactic_${i}` : `auto_${i}`,
      index: edgeIndex++,
      information: {
        result: hasError
          ? `JsonRPCTP.Err(message="Tactic failed")`
          : `Automation attempt ${i}`,
        error: hasError,
      },
    });
  }

  // 3. Multiple parallel edges between same nodes
  // Node 1 -> Node 3 (3 different tactics)
  for (let i = 0; i < 3; i++) {
    edges.push({
      source: 'node_00000001',
      target: 'node_00000003',
      label:
        i === 2
          ? `alternative_path_with_very_long_tactic_name_${i + 1}_that_includes_multiple_parameters_and_options_like_auto_with_database_hints_and_specific_lemmas_to_apply_in_sequence_making_this_a_very_detailed_command`
          : `alternative_path_${i + 1}`,
      index: edgeIndex++,
      information: {
        result: `Alternative approach ${i + 1}`,
        error: false,
      },
    });
  }

  // Node 4 -> Node 6 (2 different tactics)
  edges.push(
    {
      source: 'node_00000004',
      target: 'node_00000006',
      label: 'forward reasoning',
      index: edgeIndex++,
      information: {
        result: 'Forward chaining applied',
        error: false,
      },
    },
    {
      source: 'node_00000004',
      target: 'node_00000006',
      label: 'backward reasoning',
      index: edgeIndex++,
      information: {
        result: 'Backward chaining applied',
        error: false,
      },
    }
  );

  // 4. Backtracking edges (going back to earlier nodes)
  edges.push(
    {
      source: 'node_00000006',
      target: 'node_00000003',
      label: 'backtrack',
      index: edgeIndex++,
      information: {
        result: 'Backtracking to earlier state',
        error: false,
      },
    },
    {
      source: 'node_00000009',
      target: 'node_00000005',
      label: 'revert and retry',
      index: edgeIndex++,
      information: {
        result: 'Reverting to checkpoint',
        error: false,
      },
    }
  );

  // 5. Error edges
  edges.push(
    {
      source: 'node_00000007',
      target: 'node_00000008',
      label: 'failed_tactic',
      index: edgeIndex++,
      information: {
        result: `JsonRPCTP.Err(message="Tactic application failed")`,
        error: true,
      },
    },
    {
      source: 'node_00000000',
      target: 'node_00000005',
      label: 'error_recovery',
      index: edgeIndex++,
      information: {
        result: `JsonRPCTP.Err(message="Recovery attempt")`,
        error: true,
      },
    }
  );

  // 6. Branch and merge pattern
  edges.push(
    {
      source: 'node_00000003',
      target: 'node_00000007',
      label: 'branch_a',
      index: edgeIndex++,
      information: {
        result: 'Taking branch A',
        error: false,
      },
    },
    {
      source: 'node_00000003',
      target: 'node_00000008',
      label: 'branch_b',
      index: edgeIndex++,
      information: {
        result: 'Taking branch B',
        error: false,
      },
    }
  );

  // 7. Multiple attempts (repeating edges)
  for (let i = 0; i < 2; i++) {
    edges.push({
      source: 'node_00000009',
      target: 'node_0000000a',
      label: `attempt_${i + 1}`,
      index: edgeIndex++,
      information: {
        result: `Proof attempt ${i + 1}`,
        error: false,
      },
    });
  }

  return {
    run_id: runId,
    task_id: taskId,
    task_name: `examples/proofs/theorem_${taskId}.v#Lemma:main_theorem`,
    graph: {
      nodes,
      edges,
      information: {
        cpp_code: `void example_function(int n) {\n    // Example C++ code\n    for (int i = 0; i < n; i++) {\n        process(i);\n    }\n}`,
        cpp_spec: `example_spec =\nspecify\n  {|\n    info_name := "example_function(int)";\n    info_type := tFunction "void" ["int"%cpp_type]\n  |}\n  (\\arg{n : Z} "n" n\n   \\require (0 <= n)%Z\n   \\post result = n * 2)\n  : mpredI`,
        task_status: 'false',
        taskStatus: false,
        proofScript: `Unset SsrIdents.\nprogress verify_spec\nprogress go\nwp_while invariant.\nprogress go\n(* progress go *) (* Failed *)\n`,
      },
    },
    total_nodes: nodes.length,
    total_edges: edges.length,
  };
};
