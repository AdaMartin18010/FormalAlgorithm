import pytest
from src.graph.bellman_ford import bellman_ford, reconstruct_path


def test_basic():
    edges = [
        (0, 1, -1.0),
        (0, 2, 4.0),
        (1, 2, 3.0),
        (1, 3, 2.0),
        (1, 4, 2.0),
        (3, 2, 5.0),
        (3, 1, 1.0),
        (4, 3, -3.0),
    ]
    dist, pred = bellman_ford(edges, 0)
    assert dist[0] == 0.0
    assert dist[1] == -1.0
    assert dist[2] == 2.0
    assert dist[3] == -2.0
    assert dist[4] == 1.0
    assert reconstruct_path(pred, 3) == [0, 1, 4, 3]


def test_negative_cycle():
    edges = [
        (0, 1, 1.0),
        (1, 2, -1.0),
        (2, 0, -1.0),
    ]
    with pytest.raises(ValueError, match="Negative-weight cycle"):
        bellman_ford(edges, 0)


def test_unreachable():
    edges = [(0, 1, 5.0)]
    dist, pred = bellman_ford(edges, 0)
    assert dist[1] == 5.0
    assert 2 not in dist
    assert reconstruct_path(pred, 2) is None


def test_single_vertex():
    dist, pred = bellman_ford([], 0)
    assert dist[0] == 0.0
    assert pred == {}
