"""Tests for BFS module."""

import pytest
from src.graph.bfs import bfs, bfs_shortest_path, bfs_levels


class TestBFS:
    def test_basic(self):
        graph = {0: [1, 2], 1: [2], 2: [3], 3: []}
        assert bfs(graph, 0) == [0, 1, 2, 3]

    def test_single_vertex(self):
        graph = {0: []}
        assert bfs(graph, 0) == [0]

    def test_empty_graph(self):
        assert bfs({}, 0) == []

    def test_disconnected(self):
        graph = {0: [1], 1: [0], 2: [3], 3: [2]}
        assert bfs(graph, 0) == [0, 1]

    def test_shortest_path(self):
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        assert bfs_shortest_path(graph, 0, 3) == [0, 1, 3]
        assert bfs_shortest_path(graph, 0, 0) == [0]
        assert bfs_shortest_path(graph, 0, 5) is None

    def test_levels(self):
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        levels = bfs_levels(graph, 0)
        assert levels[0] == 0
        assert levels[1] == 1
        assert levels[2] == 1
        assert levels[3] == 2
