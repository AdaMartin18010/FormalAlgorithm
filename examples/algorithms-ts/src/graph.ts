/**
 * 图论算法集合
 * 包含遍历、最短路径、最小生成树、拓扑排序、强连通分量
 */

import { CompareFn, defaultCompare, runTests, assertEq, assertTrue, assertArrayEq } from "./utils";
import { UnionFind } from "./data_structures";

export type WeightedEdge = { u: number; v: number; w: number };
export type AdjList = number[][];
export type WeightedAdjList = { to: number; w: number }[][];

// ==================== BFS / DFS ====================

/**
 * BFS
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export function bfs(adj: AdjList, start: number): { order: number[]; dist: number[] } {
  const n = adj.length;
  const visited = new Array(n).fill(false);
  const dist = new Array(n).fill(-1);
  const order: number[] = [];
  const q: number[] = [];
  q.push(start);
  visited[start] = true;
  dist[start] = 0;
  while (q.length > 0) {
    const u = q.shift()!;
    order.push(u);
    for (const v of adj[u]) {
      if (!visited[v]) {
        visited[v] = true;
        dist[v] = dist[u] + 1;
        q.push(v);
      }
    }
  }
  return { order, dist };
}

/**
 * DFS（迭代版）
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export function dfs(adj: AdjList, start: number): number[] {
  const n = adj.length;
  const visited = new Array(n).fill(false);
  const order: number[] = [];
  const stack: number[] = [start];
  while (stack.length > 0) {
    const u = stack.pop()!;
    if (visited[u]) continue;
    visited[u] = true;
    order.push(u);
    for (let i = adj[u].length - 1; i >= 0; i--) {
      const v = adj[u][i];
      if (!visited[v]) stack.push(v);
    }
  }
  return order;
}

// ==================== 最短路径 ====================

/**
 * Dijkstra（优先队列用排序数组模拟，适用于稠密图）
 * 时间复杂度: O(V²)
 * 空间复杂度: O(V)
 */
export function dijkstra(adj: WeightedAdjList, src: number): number[] {
  const n = adj.length;
  const dist = new Array(n).fill(Infinity);
  const visited = new Array(n).fill(false);
  dist[src] = 0;
  for (let _ = 0; _ < n; _++) {
    let u = -1;
    for (let i = 0; i < n; i++) {
      if (!visited[i] && (u === -1 || dist[i] < dist[u])) u = i;
    }
    if (u === -1 || dist[u] === Infinity) break;
    visited[u] = true;
    for (const e of adj[u]) {
      if (dist[u] + e.w < dist[e.to]) {
        dist[e.to] = dist[u] + e.w;
      }
    }
  }
  return dist;
}

/**
 * Bellman-Ford（可检测负权环）
 * 时间复杂度: O(VE)
 * 空间复杂度: O(V)
 */
export function bellmanFord(edges: WeightedEdge[], n: number, src: number): number[] | null {
  const dist = new Array(n).fill(Infinity);
  dist[src] = 0;
  for (let i = 0; i < n - 1; i++) {
    for (const { u, v, w } of edges) {
      if (dist[u] !== Infinity && dist[u] + w < dist[v]) {
        dist[v] = dist[u] + w;
      }
    }
  }
  for (const { u, v, w } of edges) {
    if (dist[u] !== Infinity && dist[u] + w < dist[v]) {
      return null; // 存在负权环
    }
  }
  return dist;
}

/**
 * Floyd-Warshall（全源最短路径）
 * 时间复杂度: O(V³)
 * 空间复杂度: O(V²)
 */
export function floydWarshall(mat: number[][]): number[][] {
  const n = mat.length;
  const dist = mat.map(row => row.slice());
  for (let k = 0; k < n; k++) {
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (dist[i][k] + dist[k][j] < dist[i][j]) {
          dist[i][j] = dist[i][k] + dist[k][j];
        }
      }
    }
  }
  return dist;
}

// ==================== 最小生成树 ====================

/**
 * Kruskal
 * 时间复杂度: O(E log E)
 * 空间复杂度: O(V)
 */
export function kruskal(edges: WeightedEdge[], n: number): { mst: WeightedEdge[]; cost: number } {
  const sorted = edges.slice().sort((a, b) => a.w - b.w);
  const uf = new UnionFind(n);
  const mst: WeightedEdge[] = [];
  let cost = 0;
  for (const e of sorted) {
    if (uf.union(e.u, e.v)) {
      mst.push(e);
      cost += e.w;
      if (mst.length === n - 1) break;
    }
  }
  return { mst, cost };
}

/**
 * Prim
 * 时间复杂度: O(V²)
 * 空间复杂度: O(V)
 */
export function prim(adj: WeightedAdjList): { edges: WeightedEdge[]; cost: number } {
  const n = adj.length;
  const visited = new Array(n).fill(false);
  const minEdge = new Array(n).fill(Infinity);
  const parent = new Array(n).fill(-1);
  minEdge[0] = 0;
  let cost = 0;
  const edges: WeightedEdge[] = [];
  for (let _ = 0; _ < n; _++) {
    let u = -1;
    for (let i = 0; i < n; i++) {
      if (!visited[i] && (u === -1 || minEdge[i] < minEdge[u])) u = i;
    }
    if (u === -1 || minEdge[u] === Infinity) break;
    visited[u] = true;
    cost += minEdge[u];
    if (parent[u] !== -1) edges.push({ u: parent[u], v: u, w: minEdge[u] });
    for (const e of adj[u]) {
      if (!visited[e.to] && e.w < minEdge[e.to]) {
        minEdge[e.to] = e.w;
        parent[e.to] = u;
      }
    }
  }
  return { edges, cost };
}

// ==================== 拓扑排序 ====================

/**
 * Kahn 算法（基于入度）
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export function topologicalSort(adj: AdjList): number[] | null {
  const n = adj.length;
  const indeg = new Array(n).fill(0);
  for (const list of adj) {
    for (const v of list) indeg[v]++;
  }
  const q: number[] = [];
  for (let i = 0; i < n; i++) if (indeg[i] === 0) q.push(i);
  const order: number[] = [];
  while (q.length > 0) {
    const u = q.shift()!;
    order.push(u);
    for (const v of adj[u]) {
      indeg[v]--;
      if (indeg[v] === 0) q.push(v);
    }
  }
  return order.length === n ? order : null;
}

// ==================== 强连通分量 (Kosaraju) ====================

/**
 * Kosaraju 算法求强连通分量
 * 时间复杂度: O(V + E)
 * 空间复杂度: O(V)
 */
export function kosaraju(adj: AdjList): number[][] {
  const n = adj.length;
  const visited = new Array(n).fill(false);
  const order: number[] = [];

  function dfs1(u: number): void {
    visited[u] = true;
    for (const v of adj[u]) if (!visited[v]) dfs1(v);
    order.push(u);
  }
  for (let i = 0; i < n; i++) if (!visited[i]) dfs1(i);

  const radj: AdjList = Array.from({ length: n }, () => []);
  for (let u = 0; u < n; u++) {
    for (const v of adj[u]) radj[v].push(u);
  }

  const comp = new Array(n).fill(-1);
  let cid = 0;
  function dfs2(u: number, members: number[]): void {
    comp[u] = cid;
    members.push(u);
    for (const v of radj[u]) if (comp[v] === -1) dfs2(v, members);
  }

  const sccs: number[][] = [];
  for (let i = n - 1; i >= 0; i--) {
    const u = order[i];
    if (comp[u] === -1) {
      const members: number[] = [];
      dfs2(u, members);
      sccs.push(members);
      cid++;
    }
  }
  return sccs;
}

export function runGraphTests(): void {
  runTests("Graph", {
    "bfs": () => {
      const adj: AdjList = [[1, 2], [3], [3], []];
      const res = bfs(adj, 0);
      assertArrayEq(res.order, [0, 1, 2, 3]);
      assertArrayEq(res.dist, [0, 1, 1, 2]);
    },
    "dfs": () => {
      const adj: AdjList = [[1, 2], [3], [3], []];
      assertArrayEq(dfs(adj, 0), [0, 1, 3, 2]);
    },
    "dijkstra": () => {
      const adj: WeightedAdjList = [
        [{ to: 1, w: 4 }, { to: 2, w: 1 }],
        [{ to: 3, w: 1 }],
        [{ to: 1, w: 2 }, { to: 3, w: 5 }],
        [],
      ];
      assertArrayEq(dijkstra(adj, 0), [0, 3, 1, 4]);
    },
    "bellmanFord": () => {
      const edges: WeightedEdge[] = [
        { u: 0, v: 1, w: -1 }, { u: 0, v: 2, w: 4 },
        { u: 1, v: 2, w: 3 }, { u: 1, v: 3, w: 2 },
        { u: 3, v: 2, w: 5 }, { u: 3, v: 1, w: 1 },
      ];
      const res = bellmanFord(edges, 4, 0);
      assertTrue(res !== null);
      assertArrayEq(res!, [0, -1, 2, 1]);
    },
    "floydWarshall": () => {
      const INF = Infinity;
      const mat = [
        [0, 5, INF, 10],
        [INF, 0, 3, INF],
        [INF, INF, 0, 1],
        [INF, INF, INF, 0],
      ];
      const res = floydWarshall(mat);
      assertEq(res[0][3], 9);
      assertEq(res[0][2], 8);
    },
    "kruskal": () => {
      const edges: WeightedEdge[] = [
        { u: 0, v: 1, w: 10 }, { u: 0, v: 2, w: 6 }, { u: 0, v: 3, w: 5 },
        { u: 1, v: 3, w: 15 }, { u: 2, v: 3, w: 4 },
      ];
      const res = kruskal(edges, 4);
      assertEq(res.cost, 19);
      assertEq(res.mst.length, 3);
    },
    "prim": () => {
      const adj: WeightedAdjList = [
        [{ to: 1, w: 2 }, { to: 3, w: 6 }],
        [{ to: 0, w: 2 }, { to: 2, w: 3 }, { to: 3, w: 8 }, { to: 4, w: 5 }],
        [{ to: 1, w: 3 }, { to: 4, w: 7 }],
        [{ to: 0, w: 6 }, { to: 1, w: 8 }, { to: 4, w: 9 }],
        [{ to: 1, w: 5 }, { to: 2, w: 7 }, { to: 3, w: 9 }],
      ];
      const res = prim(adj);
      assertEq(res.cost, 16);
    },
    "topologicalSort": () => {
      const adj: AdjList = [[1, 2], [3], [3], []];
      const res = topologicalSort(adj);
      assertTrue(res !== null);
      assertEq(res![0], 0);
    },
    "kosaraju": () => {
      const adj: AdjList = [[1], [2, 4], [3, 5], [0, 6], [5], [4], [5, 7], [6]];
      const sccs = kosaraju(adj);
      assertEq(sccs.length, 4);
    },
  });
}
