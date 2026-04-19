package graph;

import java.util.*;

/**
 * Breadth-First Search implementation.
 * Time complexity: O(V + E). Space complexity: O(V).
 */
public class BFS {

    /**
     * Returns vertices in BFS order starting from start.
     */
    public static List<Integer> traverse(Map<Integer, List<Integer>> graph, int start) {
        List<Integer> order = new ArrayList<>();
        if (!graph.containsKey(start)) {
            return order;
        }
        Set<Integer> visited = new HashSet<>();
        Queue<Integer> queue = new LinkedList<>();
        visited.add(start);
        queue.add(start);

        while (!queue.isEmpty()) {
            int v = queue.poll();
            order.add(v);
            for (int neighbor : graph.getOrDefault(v, Collections.emptyList())) {
                if (!visited.contains(neighbor)) {
                    visited.add(neighbor);
                    queue.add(neighbor);
                }
            }
        }
        return order;
    }

    /**
     * Returns the shortest path from start to goal, or null if no path exists.
     */
    public static List<Integer> shortestPath(Map<Integer, List<Integer>> graph, int start, int goal) {
        if (start == goal) {
            return Collections.singletonList(start);
        }
        if (!graph.containsKey(start)) {
            return null;
        }
        Set<Integer> visited = new HashSet<>();
        visited.add(start);
        Queue<List<Integer>> queue = new LinkedList<>();
        queue.add(new ArrayList<>(Collections.singletonList(start)));

        while (!queue.isEmpty()) {
            List<Integer> path = queue.poll();
            int v = path.get(path.size() - 1);
            for (int neighbor : graph.getOrDefault(v, Collections.emptyList())) {
                if (neighbor == goal) {
                    List<Integer> result = new ArrayList<>(path);
                    result.add(neighbor);
                    return result;
                }
                if (!visited.contains(neighbor)) {
                    visited.add(neighbor);
                    List<Integer> newPath = new ArrayList<>(path);
                    newPath.add(neighbor);
                    queue.add(newPath);
                }
            }
        }
        return null;
    }
}
