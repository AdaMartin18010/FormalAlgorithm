package graph;

import java.util.*;

/**
 * 图的广度优先搜索(BFS)和深度优先搜索(DFS)
 */
public class GraphTraversal {
    
    private final int vertices;
    private final List<List<Integer>> adjacencyList;
    
    public GraphTraversal(int vertices) {
        this.vertices = vertices;
        this.adjacencyList = new ArrayList<>(vertices);
        for (int i = 0; i < vertices; i++) {
            adjacencyList.add(new ArrayList<>());
        }
    }
    
    public void addEdge(int from, int to) {
        adjacencyList.get(from).add(to);
    }
    
    /**
     * 广度优先搜索 (BFS)
     * 时间复杂度: O(V + E)
     * 空间复杂度: O(V)
     */
    public List<Integer> bfs(int start) {
        List<Integer> result = new ArrayList<>();
        boolean[] visited = new boolean[vertices];
        Queue<Integer> queue = new LinkedList<>();
        
        visited[start] = true;
        queue.offer(start);
        
        while (!queue.isEmpty()) {
            int vertex = queue.poll();
            result.add(vertex);
            
            for (int neighbor : adjacencyList.get(vertex)) {
                if (!visited[neighbor]) {
                    visited[neighbor] = true;
                    queue.offer(neighbor);
                }
            }
        }
        
        return result;
    }
    
    /**
     * BFS寻找最短路径（无权图）
     */
    public List<Integer> bfsShortestPath(int start, int target) {
        boolean[] visited = new boolean[vertices];
        int[] parent = new int[vertices];
        Arrays.fill(parent, -1);
        
        Queue<Integer> queue = new LinkedList<>();
        visited[start] = true;
        queue.offer(start);
        
        while (!queue.isEmpty()) {
            int vertex = queue.poll();
            
            if (vertex == target) {
                return reconstructPath(start, target, parent);
            }
            
            for (int neighbor : adjacencyList.get(vertex)) {
                if (!visited[neighbor]) {
                    visited[neighbor] = true;
                    parent[neighbor] = vertex;
                    queue.offer(neighbor);
                }
            }
        }
        
        return new ArrayList<>(); // 未找到路径
    }
    
    /**
     * 深度优先搜索 (DFS) - 递归实现
     */
    public List<Integer> dfs(int start) {
        List<Integer> result = new ArrayList<>();
        boolean[] visited = new boolean[vertices];
        dfsRecursive(start, visited, result);
        return result;
    }
    
    private void dfsRecursive(int vertex, boolean[] visited, List<Integer> result) {
        visited[vertex] = true;
        result.add(vertex);
        
        for (int neighbor : adjacencyList.get(vertex)) {
            if (!visited[neighbor]) {
                dfsRecursive(neighbor, visited, result);
            }
        }
    }
    
    /**
     * 深度优先搜索 (DFS) - 迭代实现
     */
    public List<Integer> dfsIterative(int start) {
        List<Integer> result = new ArrayList<>();
        boolean[] visited = new boolean[vertices];
        Stack<Integer> stack = new Stack<>();
        
        stack.push(start);
        
        while (!stack.isEmpty()) {
            int vertex = stack.pop();
            
            if (!visited[vertex]) {
                visited[vertex] = true;
                result.add(vertex);
                
                // 将邻居压入栈（逆序以保证正确遍历顺序）
                List<Integer> neighbors = adjacencyList.get(vertex);
                for (int i = neighbors.size() - 1; i >= 0; i--) {
                    int neighbor = neighbors.get(i);
                    if (!visited[neighbor]) {
                        stack.push(neighbor);
                    }
                }
            }
        }
        
        return result;
    }
    
    /**
     * 检测图中是否存在环（使用DFS）
     */
    public boolean hasCycle() {
        boolean[] visited = new boolean[vertices];
        boolean[] recStack = new boolean[vertices];
        
        for (int i = 0; i < vertices; i++) {
            if (!visited[i]) {
                if (hasCycleUtil(i, visited, recStack)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    private boolean hasCycleUtil(int vertex, boolean[] visited, boolean[] recStack) {
        visited[vertex] = true;
        recStack[vertex] = true;
        
        for (int neighbor : adjacencyList.get(vertex)) {
            if (!visited[neighbor]) {
                if (hasCycleUtil(neighbor, visited, recStack)) {
                    return true;
                }
            } else if (recStack[neighbor]) {
                return true; // 发现回边
            }
        }
        
        recStack[vertex] = false;
        return false;
    }
    
    /**
     * 拓扑排序（Kahn算法 - BFS）
     */
    public List<Integer> topologicalSortKahn() {
        int[] inDegree = new int[vertices];
        
        // 计算入度
        for (int i = 0; i < vertices; i++) {
            for (int neighbor : adjacencyList.get(i)) {
                inDegree[neighbor]++;
            }
        }
        
        Queue<Integer> queue = new LinkedList<>();
        for (int i = 0; i < vertices; i++) {
            if (inDegree[i] == 0) {
                queue.offer(i);
            }
        }
        
        List<Integer> result = new ArrayList<>();
        int count = 0;
        
        while (!queue.isEmpty()) {
            int vertex = queue.poll();
            result.add(vertex);
            count++;
            
            for (int neighbor : adjacencyList.get(vertex)) {
                inDegree[neighbor]--;
                if (inDegree[neighbor] == 0) {
                    queue.offer(neighbor);
                }
            }
        }
        
        // 如果count不等于顶点数，说明存在环
        return count == vertices ? result : new ArrayList<>();
    }
    
    private List<Integer> reconstructPath(int start, int target, int[] parent) {
        List<Integer> path = new LinkedList<>();
        int current = target;
        
        while (current != -1) {
            ((LinkedList<Integer>) path).addFirst(current);
            if (current == start) break;
            current = parent[current];
        }
        
        return path;
    }
    
    // 测试
    public static void main(String[] args) {
        GraphTraversal graph = new GraphTraversal(6);
        
        // 构建图
        graph.addEdge(0, 1);
        graph.addEdge(0, 2);
        graph.addEdge(1, 3);
        graph.addEdge(1, 4);
        graph.addEdge(2, 4);
        graph.addEdge(3, 5);
        graph.addEdge(4, 5);
        
        System.out.println("BFS from 0: " + graph.bfs(0));
        System.out.println("DFS from 0: " + graph.dfs(0));
        System.out.println("DFS Iterative from 0: " + graph.dfsIterative(0));
        System.out.println("BFS Shortest Path 0 -> 5: " + graph.bfsShortestPath(0, 5));
        System.out.println("Has cycle: " + graph.hasCycle());
        System.out.println("Topological Sort (Kahn): " + graph.topologicalSortKahn());
    }
}
