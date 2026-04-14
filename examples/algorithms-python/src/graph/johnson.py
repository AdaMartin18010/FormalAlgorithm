"""
Johnson 全对最短路径算法 - Python 版本

通过重赋权将负权边转化为非负权边，再对每个顶点运行 Dijkstra。
支持负权边，可检测负权环。
对标: CLRS Chapter 25.3
"""

import heapq
from typing import List, Optional, Tuple


def johnson(
    n: int, edges: List[Tuple[int, int, float]]
) -> Tuple[List[List[float]], List[List[Optional[int]]]]:
    """
    Johnson 全对最短路径算法。

    参数:
        n: 顶点数量（编号 0 到 n-1）
        edges: 边列表，每条边为 (u, v, weight)

    返回:
        (dist, nxt) 元组。
        dist[i][j] 为 i 到 j 的最短距离；nxt 为后继矩阵，用于路径重建。

    异常:
        ValueError: 若图中存在负权环
    """
    from src.graph.bellman_ford import bellman_ford

    inf = float("inf")

    # 1. 添加超级源点，运行 Bellman-Ford
    s = n
    bf_edges = list(edges)
    for v in range(n):
        bf_edges.append((s, v, 0.0))

    dist_bf, _ = bellman_ford(bf_edges, s)

    # 2. 计算势能 h
    h = [dist_bf.get(v, inf) for v in range(n)]

    # 3. 重新赋权
    reweighted = []
    for u, v, w in edges:
        new_w = w + h[u] - h[v]
        reweighted.append((u, v, new_w))

    # 4. 对每个顶点运行 Dijkstra
    dist = [[inf] * n for _ in range(n)]
    nxt = [[None] * n for _ in range(n)]

    for src in range(n):
        d, nx = _dijkstra_single(n, reweighted, src)
        for v in range(n):
            if src == v:
                dist[src][v] = 0.0
                continue
            if d[v] != inf:
                dist[src][v] = d[v] - h[src] + h[v]
                nxt[src][v] = nx[v]

    return dist, nxt


def _dijkstra_single(
    n: int, edges: List[Tuple[int, int, float]], source: int
) -> Tuple[List[float], List[Optional[int]]]:
    """在重新赋权后的图上从 source 运行 Dijkstra 算法。"""
    adj = [[] for _ in range(n)]
    for u, v, w in edges:
        adj[u].append((v, w))

    inf = float("inf")
    dist = [inf] * n
    nxt: List[Optional[int]] = [None] * n
    visited = [False] * n

    dist[source] = 0.0
    heap = [(0.0, source)]

    while heap:
        d, u = heapq.heappop(heap)
        if visited[u]:
            continue
        if d > dist[u]:
            continue
        visited[u] = True

        for v, w in adj[u]:
            if visited[v]:
                continue
            nd = d + w
            if nd < dist[v]:
                dist[v] = nd
                nxt[v] = v if u == source else nxt[u]
                heapq.heappush(heap, (nd, v))

    return dist, nxt


def reconstruct_path(
    nxt: List[List[Optional[int]]], u: int, v: int
) -> Optional[List[int]]:
    """
    根据后继矩阵重建从 u 到 v 的最短路径。

    若 u == v，返回 [u]；
    若不可达，返回 None。
    """
    if u == v:
        return [u]
    if nxt[u][v] is None:
        return None
    path = [u]
    at = u
    while at != v:
        nxt_at = nxt[at][v]
        if nxt_at is None:
            return None
        at = nxt_at
        path.append(at)
    return path
