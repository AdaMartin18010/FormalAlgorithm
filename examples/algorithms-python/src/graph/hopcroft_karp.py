"""
Hopcroft-Karp 二分图最大匹配算法 - Python 版本

时间复杂度: O(E * sqrt(V))
对标: CLRS Chapter 26 问题 26-6
"""

from collections import deque
from typing import List, Optional, Tuple


def hopcroft_karp(
    n_left: int, n_right: int, edges: List[Tuple[int, int]]
) -> Tuple[int, List[Optional[int]]]:
    """
    Hopcroft-Karp 二分图最大匹配算法。

    参数:
        n_left: 左部顶点数（编号 0..n_left-1）
        n_right: 右部顶点数（编号 0..n_right-1）
        edges: 边列表，每条边为 (u, v)

    返回:
        (matching_size, pair_left) 元组。
        pair_left[u] 为左部顶点 u 的匹配对象，未匹配时为 None。
    """
    adj = [[] for _ in range(n_left)]
    for u, v in edges:
        if 0 <= u < n_left and 0 <= v < n_right:
            adj[u].append(v)

    pair_left: List[Optional[int]] = [None] * n_left
    pair_right: List[Optional[int]] = [None] * n_right
    dist = [0] * n_left

    matching_size = 0

    def bfs() -> bool:
        queue = deque()
        for u in range(n_left):
            if pair_left[u] is None:
                dist[u] = 0
                queue.append(u)
            else:
                dist[u] = -1

        found = False
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                u2 = pair_right[v]
                if u2 is not None:
                    if dist[u2] == -1:
                        dist[u2] = dist[u] + 1
                        queue.append(u2)
                else:
                    found = True
        return found

    def dfs(u: int) -> bool:
        for v in adj[u]:
            u2 = pair_right[v]
            if u2 is not None:
                if dist[u2] == dist[u] + 1 and dfs(u2):
                    pair_left[u] = v
                    pair_right[v] = u
                    return True
            else:
                pair_left[u] = v
                pair_right[v] = u
                return True
        dist[u] = -1
        return False

    while bfs():
        for u in range(n_left):
            if pair_left[u] is None and dfs(u):
                matching_size += 1

    return matching_size, pair_left
