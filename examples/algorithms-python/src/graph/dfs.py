"""Depth-First Search (DFS) implementation.

DFS explores a graph by going as deep as possible before backtracking.
Time complexity: O(V + E), Space complexity: O(V).
"""

from typing import Dict, List, Set, Optional, TypeVar

T = TypeVar("T")


def dfs(graph: Dict[T, List[T]], start: T) -> List[T]:
    """Perform iterative DFS traversal and return the order of visited vertices.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.

    Returns:
        List of vertices in DFS order.

    Examples:
        >>> graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        >>> dfs(graph, 0)
        [0, 2, 3, 1]
    """
    if start not in graph:
        return []
    visited: Set[T] = set()
    stack: List[T] = [start]
    order: List[T] = []
    visited.add(start)

    while stack:
        vertex = stack.pop()
        order.append(vertex)
        # Reverse neighbors to maintain a predictable order
        for neighbor in reversed(graph.get(vertex, [])):
            if neighbor not in visited:
                visited.add(neighbor)
                stack.append(neighbor)
    return order


def dfs_recursive(graph: Dict[T, List[T]], start: T) -> List[T]:
    """Perform recursive DFS traversal and return the order of visited vertices.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.

    Returns:
        List of vertices in DFS order.
    """
    visited: Set[T] = set()
    order: List[T] = []

    def _dfs(vertex: T) -> None:
        visited.add(vertex)
        order.append(vertex)
        for neighbor in graph.get(vertex, []):
            if neighbor not in visited:
                _dfs(neighbor)

    if start in graph:
        _dfs(start)
    return order


def has_path(graph: Dict[T, List[T]], start: T, goal: T) -> bool:
    """Check if a path exists from start to goal.

    Args:
        graph: Adjacency list representation.
        start: Starting vertex.
        goal: Target vertex.

    Returns:
        True if a path exists, False otherwise.
    """
    if start == goal:
        return True
    if start not in graph or goal not in graph:
        return False

    visited: Set[T] = set()
    stack: List[T] = [start]
    visited.add(start)

    while stack:
        vertex = stack.pop()
        for neighbor in graph.get(vertex, []):
            if neighbor == goal:
                return True
            if neighbor not in visited:
                visited.add(neighbor)
                stack.append(neighbor)
    return False


def topological_sort(graph: Dict[T, List[T]]) -> Optional[List[T]]:
    """Return a topological ordering of a directed acyclic graph (DAG).

    Args:
        graph: Adjacency list representation of a DAG.

    Returns:
        Topologically sorted list, or None if the graph contains a cycle.
    """
    visited: Set[T] = set()
    temp: Set[T] = set()
    order: List[T] = []

    def _visit(vertex: T) -> bool:
        if vertex in temp:
            return False  # Cycle detected
        if vertex in visited:
            return True
        temp.add(vertex)
        for neighbor in graph.get(vertex, []):
            if not _visit(neighbor):
                return False
        temp.remove(vertex)
        visited.add(vertex)
        order.append(vertex)
        return True

    for vertex in graph:
        if vertex not in visited:
            if not _visit(vertex):
                return None
    return list(reversed(order))
