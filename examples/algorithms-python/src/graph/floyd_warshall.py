"""
Floyd-Warshall 全对最短路径算法 - Python 版本

对标: CLRS Chapter 25.2
"""

from typing import List, Optional, Tuple


def floyd_warshall(
    n: int, edges: List[Tuple[int, int, float]]
) -> Tuple[List[List[float]], List[List[Optional[int]]]]:
    """
    Floyd-Warshall 全对最短路径算法。

    参数:
        n: 顶点数量（编号 0 到 n-1）
        edges: 边列表，每条边为 (u, v, weight)

    返回:
        (dist, nxt) 元组。
        dist[i][j] 为 i 到 j 的最短距离；nxt 为后继矩阵，用于路径重建。

    异常:
        ValueError: 若图中存在负权环
    """
    inf = float("inf")
    dist = [[inf] * n for _ in range(n)]
    nxt = [[None] * n for _ in range(n)]

    for i in range(n):
        dist[i][i] = 0.0

    for u, v, w in edges:
        if w < dist[u][v]:
            dist[u][v] = w
            nxt[u][v] = v

    for k in range(n):
        for i in range(n):
            if dist[i][k] == inf:
                continue
            for j in range(n):
                if dist[k][j] == inf:
                    continue
                via = dist[i][k] + dist[k][j]
                if via < dist[i][j]:
                    dist[i][j] = via
                    nxt[i][j] = nxt[i][k]

    # 负权环检测
    for i in range(n):
        if dist[i][i] < 0:
            raise ValueError("Negative-weight cycle detected")

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
