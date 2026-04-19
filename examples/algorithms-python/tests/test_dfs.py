"""Tests for DFS module."""

import pytest
from src.graph.dfs import dfs, dfs_recursive, has_path, topological_sort


class TestDFS:
    def test_basic(self):
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        result = dfs(graph, 0)
        assert result[0] == 0
        assert set(result) == {0, 1, 2, 3}

    def test_single_vertex(self):
        graph = {0: []}
        assert dfs(graph, 0) == [0]

    def test_empty_graph(self):
        assert dfs({}, 0) == []

    def test_recursive(self):
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        result = dfs_recursive(graph, 0)
        assert result[0] == 0
        assert set(result) == {0, 1, 2, 3}

    def test_has_path(self):
        graph = {0: [1, 2], 1: [3], 2: [], 3: []}
        assert has_path(graph, 0, 3) is True
        assert has_path(graph, 2, 3) is False
        assert has_path(graph, 0, 0) is True

    def test_topological_sort(self):
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        order = topological_sort(graph)
        assert order is not None
        # 0 must come before 1 and 2
        assert order.index(0) < order.index(1)
        assert order.index(0) < order.index(2)
        # 1 and 2 must come before 3
        assert order.index(1) < order.index(3)
        assert order.index(2) < order.index(3)

    def test_topological_sort_cycle(self):
        graph = {0: [1], 1: [2], 2: [0]}
        assert topological_sort(graph) is None
