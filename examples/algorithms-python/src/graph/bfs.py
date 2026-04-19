"""Breadth-First Search (BFS) implementation.

BFS explores a graph level by level from a source vertex.
Time complexity: O(V + E), Space complexity: O(V).
"""

from collections import deque
from typing import Dict, List, Set, Optional, Callable, TypeVar

T = TypeVar("T")


def bfs(graph: Dict[T, List[T]], start: T) -> List[T]:
    """Perform BFS traversal and return the order of visited vertices.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.

    Returns:
        List of vertices in BFS order.

    Examples:
        >>> graph = {0: [1, 2], 1: [2], 2: [3], 3: []}
        >>> bfs(graph, 0)
        [0, 1, 2, 3]
    """
    if start not in graph:
        return []
    visited: Set[T] = set()
    queue: deque[T] = deque([start])
    order: List[T] = []
    visited.add(start)

    while queue:
        vertex = queue.popleft()
        order.append(vertex)
        for neighbor in graph.get(vertex, []):
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    return order


def bfs_shortest_path(graph: Dict[T, List[T]], start: T, goal: T) -> Optional[List[T]]:
    """Find the shortest path from start to goal using BFS.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.
        goal: Target vertex.

    Returns:
        Shortest path as a list of vertices, or None if no path exists.
    """
    if start == goal:
        return [start]
    if start not in graph or goal not in graph:
        return None

    queue: deque[List[T]] = deque([[start]])
    visited: Set[T] = {start}

    while queue:
        path = queue.popleft()
        vertex = path[-1]
        for neighbor in graph.get(vertex, []):
            if neighbor == goal:
                return path + [neighbor]
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(path + [neighbor])
    return None


def bfs_levels(graph: Dict[T, List[T]], start: T) -> Dict[T, int]:
    """Return the distance (number of edges) from start to each reachable vertex.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.

    Returns:
        Dictionary mapping vertex to distance from start.
    """
    if start not in graph:
        return {}
    distances: Dict[T, int] = {start: 0}
    queue: deque[T] = deque([start])

    while queue:
        vertex = queue.popleft()
        for neighbor in graph.get(vertex, []):
            if neighbor not in distances:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    return distances
