package graph;

import java.util.*;

/**
 * Depth-First Search implementation.
 * Time complexity: O(V + E). Space complexity: O(V).
 */
public class DFS {

    /**
     * Returns vertices in DFS order starting from start.
     */
    public static List<Integer> traverse(Map<Integer, List<Integer>> graph, int start) {
        List<Integer> order = new ArrayList<>();
        if (!graph.containsKey(start)) {
            return order;
        }
        Set<Integer> visited = new HashSet<>();
        Deque<Integer> stack = new ArrayDeque<>();
        visited.add(start);
        stack.push(start);

        while (!stack.isEmpty()) {
            int v = stack.pop();
            order.add(v);
            List<Integer> neighbors = graph.getOrDefault(v, Collections.emptyList());
            for (int i = neighbors.size() - 1; i >= 0; i--) {
                int neighbor = neighbors.get(i);
                if (!visited.contains(neighbor)) {
                    visited.add(neighbor);
                    stack.push(neighbor);
                }
            }
        }
        return order;
    }

    /**
     * Checks if a path exists from start to goal.
     */
    public static boolean hasPath(Map<Integer, List<Integer>> graph, int start, int goal) {
        if (start == goal) {
            return true;
        }
        if (!graph.containsKey(start)) {
            return false;
        }
        Set<Integer> visited = new HashSet<>();
        Deque<Integer> stack = new ArrayDeque<>();
        visited.add(start);
        stack.push(start);

        while (!stack.isEmpty()) {
            int v = stack.pop();
            for (int neighbor : graph.getOrDefault(v, Collections.emptyList())) {
                if (neighbor == goal) {
                    return true;
                }
                if (!visited.contains(neighbor)) {
                    visited.add(neighbor);
                    stack.push(neighbor);
                }
            }
        }
        return false;
    }
}
