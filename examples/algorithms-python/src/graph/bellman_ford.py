"""
Bellman-Ford 单源最短路径算法 - Python 版本

支持负权边，可检测负权环。
对标: CLRS Chapter 24.1
"""

from typing import Dict, List, Optional, Tuple, TypeVar

V = TypeVar("V")


def bellman_ford(
    edges: List[Tuple[V, V, float]], source: V
) -> Tuple[Dict[V, float], Dict[V, V]]:
    """
    Bellman-Ford 单源最短路径算法。

    参数:
        edges: 边列表，每条边为 (from, to, weight)
        source: 源点

    返回:
        (distances, predecessors) 元组。
        distances 中不可达顶点的距离为 float('inf')。

    异常:
        ValueError: 若图中存在从源点可达的负权环
    """
    vertices = {source}
    for u, v, _ in edges:
        vertices.add(u)
        vertices.add(v)

    n = len(vertices)
    inf = float("inf")

    distances: Dict[V, float] = {v: inf for v in vertices}
    distances[source] = 0.0
    predecessors: Dict[V, V] = {}

    for _ in range(n - 1):
        updated = False
        for u, v, w in edges:
            du = distances.get(u, inf)
            if du == inf:
                continue
            new_d = du + w
            if new_d < distances.get(v, inf):
                distances[v] = new_d
                predecessors[v] = u
                updated = True
        if not updated:
            break

    # 负权环检测
    for u, v, w in edges:
        du = distances.get(u, inf)
        if du == inf:
            continue
        if du + w < distances.get(v, inf):
            raise ValueError("Negative-weight cycle detected")

    return distances, predecessors


def reconstruct_path(predecessors: Dict[V, V], target: V) -> Optional[List[V]]:
    """
    根据前驱字典重建从源点到 target 的最短路径。

    若 target 无前驱记录（包括 target 即为源点的情况），返回 None。
    """
    if target not in predecessors:
        return None
    path = [target]
    current = target
    while current in predecessors:
        current = predecessors[current]
        path.append(current)
    path.reverse()
    return path
