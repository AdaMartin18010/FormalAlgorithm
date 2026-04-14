import pytest
from src.graph.hopcroft_karp import hopcroft_karp


def test_perfect_matching():
    edges = [
        (0, 0),
        (0, 1),
        (1, 1),
        (1, 2),
        (2, 2),
        (2, 3),
        (3, 3),
    ]
    size, pair_left = hopcroft_karp(4, 4, edges)
    assert size == 4
    assert None not in pair_left


def test_maximum_matching():
    edges = [
        (0, 0),
        (0, 1),
        (1, 0),
        (1, 1),
        (2, 0),
        (2, 1),
    ]
    size, pair_left = hopcroft_karp(3, 2, edges)
    assert size == 2
    assert pair_left.count(None) == 1


def test_empty_graph():
    size, pair_left = hopcroft_karp(3, 3, [])
    assert size == 0
    assert all(p is None for p in pair_left)


def test_single_edge():
    size, pair_left = hopcroft_karp(2, 2, [(0, 1)])
    assert size == 1
    assert pair_left[0] == 1
    assert pair_left[1] is None


def test_disconnected():
    edges = [(0, 0), (2, 1)]
    size, pair_left = hopcroft_karp(3, 2, edges)
    assert size == 2
