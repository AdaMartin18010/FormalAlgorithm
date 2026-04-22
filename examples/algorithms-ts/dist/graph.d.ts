/**
 * 图论算法集合
 * 包含遍历、最短路径、最小生成树、拓扑排序、强连通分量
 */
export type WeightedEdge = {
    u: number;
    v: number;
    w: number;
};
export type AdjList = number[][];
export type WeightedAdjList = {
    to: number;
    w: number;
}[][];
/**
 * BFS
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export declare function bfs(adj: AdjList, start: number): {
    order: number[];
    dist: number[];
};
/**
 * DFS（迭代版）
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export declare function dfs(adj: AdjList, start: number): number[];
/**
 * Dijkstra（优先队列用排序数组模拟，适用于稠密图）
 * 时间复杂度: O(V²)
 * 空间复杂度: O(V)
 */
export declare function dijkstra(adj: WeightedAdjList, src: number): number[];
/**
 * Bellman-Ford（可检测负权环）
 * 时间复杂度: O(VE)
 * 空间复杂度: O(V)
 */
export declare function bellmanFord(edges: WeightedEdge[], n: number, src: number): number[] | null;
/**
 * Floyd-Warshall（全源最短路径）
 * 时间复杂度: O(V³)
 * 空间复杂度: O(V²)
 */
export declare function floydWarshall(mat: number[][]): number[][];
/**
 * Kruskal
 * 时间复杂度: O(E log E)
 * 空间复杂度: O(V)
 */
export declare function kruskal(edges: WeightedEdge[], n: number): {
    mst: WeightedEdge[];
    cost: number;
};
/**
 * Prim
 * 时间复杂度: O(V²)
 * 空间复杂度: O(V)
 */
export declare function prim(adj: WeightedAdjList): {
    edges: WeightedEdge[];
    cost: number;
};
/**
 * Kahn 算法（基于入度）
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export declare function topologicalSort(adj: AdjList): number[] | null;
/**
 * Kosaraju 算法求强连通分量
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export declare function kosaraju(adj: AdjList): number[][];
export declare function runGraphTests(): void;
//# sourceMappingURL=graph.d.ts.map