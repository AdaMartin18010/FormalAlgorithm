import pytest
from src.graph.johnson import johnson, reconstruct_path


def test_basic():
    edges = [
        (0, 1, 3.0),
        (0, 3, 7.0),
        (1, 0, 8.0),
        (1, 2, 2.0),
        (2, 0, 5.0),
        (2, 3, 1.0),
        (3, 0, 2.0),
    ]
    dist, nxt = johnson(4, edges)
    assert dist[0][2] == pytest.approx(5.0)
    assert dist[1][3] == pytest.approx(3.0)
    assert dist[3][2] == pytest.approx(7.0)
    assert reconstruct_path(nxt, 0, 3) == [0, 1, 2, 3]


def test_negative_edges():
    edges = [
        (0, 1, -5.0),
        (0, 2, 2.0),
        (1, 2, 4.0),
        (2, 3, 1.0),
        (3, 1, -3.0),
    ]
    dist, nxt = johnson(4, edges)
    assert dist[0][1] == pytest.approx(-5.0)
    assert dist[0][3] == pytest.approx(0.0)
    assert dist[3][1] == pytest.approx(-3.0)


def test_negative_cycle():
    edges = [
        (0, 1, 1.0),
        (1, 2, -3.0),
        (2, 0, 1.0),
    ]
    with pytest.raises(ValueError, match="Negative-weight cycle"):
        johnson(3, edges)


def test_disconnected():
    edges = [(0, 1, 5.0)]
    dist, nxt = johnson(3, edges)
    assert dist[0][1] == pytest.approx(5.0)
    assert dist[0][2] == float("inf")
    assert reconstruct_path(nxt, 0, 2) is None


def test_same_vertex():
    dist, nxt = johnson(2, [])
    assert dist[0][0] == 0.0
    assert reconstruct_path(nxt, 0, 0) == [0]
