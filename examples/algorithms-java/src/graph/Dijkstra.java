package graph;

import java.util.*;

/**
 * Dijkstra最短路径算法
 * 时间复杂度: O((V+E) log V) 使用优先队列
 * 空间复杂度: O(V)
 * 适用于非负权重图
 */
public class Dijkstra {
    
    // 邻接表表示的图
    private final int vertices;
    private final List<List<Edge>> adjacencyList;
    
    public Dijkstra(int vertices) {
        this.vertices = vertices;
        this.adjacencyList = new ArrayList<>(vertices);
        for (int i = 0; i < vertices; i++) {
            adjacencyList.add(new ArrayList<>());
        }
    }
    
    /**
     * 添加边
     * @param from 起点
     * @param to 终点
     * @param weight 权重
     */
    public void addEdge(int from, int to, int weight) {
        adjacencyList.get(from).add(new Edge(to, weight));
    }
    
    /**
     * 计算从源点到所有其他顶点的最短路径
     * @param source 源点
     * @return 距离数组
     */
    public int[] shortestPath(int source) {
        int[] dist = new int[vertices];
        Arrays.fill(dist, Integer.MAX_VALUE);
        dist[source] = 0;
        
        // 优先队列: (距离, 顶点)
        PriorityQueue<Node> pq = new PriorityQueue<>(Comparator.comparingInt(n -> n.distance));
        pq.offer(new Node(source, 0));
        
        boolean[] visited = new boolean[vertices];
        
        while (!pq.isEmpty()) {
            Node node = pq.poll();
            int u = node.vertex;
            
            if (visited[u]) continue;
            visited[u] = true;
            
            for (Edge edge : adjacencyList.get(u)) {
                int v = edge.to;
                int weight = edge.weight;
                
                if (!visited[v] && dist[u] != Integer.MAX_VALUE && 
                    dist[u] + weight < dist[v]) {
                    dist[v] = dist[u] + weight;
                    pq.offer(new Node(v, dist[v]));
                }
            }
        }
        
        return dist;
    }
    
    /**
     * 计算最短路径并返回路径信息
     */
    public Result shortestPathWithPath(int source) {
        int[] dist = new int[vertices];
        int[] parent = new int[vertices];
        Arrays.fill(dist, Integer.MAX_VALUE);
        Arrays.fill(parent, -1);
        dist[source] = 0;
        
        PriorityQueue<Node> pq = new PriorityQueue<>(Comparator.comparingInt(n -> n.distance));
        pq.offer(new Node(source, 0));
        
        boolean[] visited = new boolean[vertices];
        
        while (!pq.isEmpty()) {
            Node node = pq.poll();
            int u = node.vertex;
            
            if (visited[u]) continue;
            visited[u] = true;
            
            for (Edge edge : adjacencyList.get(u)) {
                int v = edge.to;
                int weight = edge.weight;
                
                if (!visited[v] && dist[u] != Integer.MAX_VALUE && 
                    dist[u] + weight < dist[v]) {
                    dist[v] = dist[u] + weight;
                    parent[v] = u;
                    pq.offer(new Node(v, dist[v]));
                }
            }
        }
        
        return new Result(dist, parent);
    }
    
    /**
     * 获取从源点到目标点的路径
     */
    public List<Integer> getPath(int source, int target, int[] parent) {
        List<Integer> path = new ArrayList<>();
        int current = target;
        
        while (current != -1) {
            path.add(current);
            if (current == source) break;
            current = parent[current];
        }
        
        Collections.reverse(path);
        return path;
    }
    
    // 边类
    private static class Edge {
        int to;
        int weight;
        
        Edge(int to, int weight) {
            this.to = to;
            this.weight = weight;
        }
    }
    
    // 节点类（用于优先队列）
    private static class Node {
        int vertex;
        int distance;
        
        Node(int vertex, int distance) {
            this.vertex = vertex;
            this.distance = distance;
        }
    }
    
    // 结果类
    public static class Result {
        public final int[] distances;
        public final int[] parent;
        
        Result(int[] distances, int[] parent) {
            this.distances = distances;
            this.parent = parent;
        }
    }
    
    // 测试
    public static void main(String[] args) {
        Dijkstra graph = new Dijkstra(6);
        
        // 构建图
        graph.addEdge(0, 1, 4);
        graph.addEdge(0, 2, 2);
        graph.addEdge(1, 2, 1);
        graph.addEdge(1, 3, 5);
        graph.addEdge(2, 3, 8);
        graph.addEdge(2, 4, 10);
        graph.addEdge(3, 4, 2);
        graph.addEdge(3, 5, 6);
        graph.addEdge(4, 5, 3);
        
        int source = 0;
        Result result = graph.shortestPathWithPath(source);
        
        System.out.println("从顶点 " + source + " 到各顶点的最短距离:");
        for (int i = 0; i < 6; i++) {
            System.out.println("到顶点 " + i + ": " + result.distances[i]);
        }
        
        System.out.println("\n路径示例 (0 -> 5):");
        List<Integer> path = graph.getPath(source, 5, result.parent);
        System.out.println(path);
    }
}
