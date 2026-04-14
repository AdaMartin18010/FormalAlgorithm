"""计数排序测试"""

import pytest
from src.sorting.counting_sort import counting_sort, counting_sort_by_key


def test_empty():
    assert counting_sort([], 0) == []


def test_single_element():
    assert counting_sort([5], 10) == [5]


def test_basic():
    arr = [4, 2, 2, 8, 3, 3, 1]
    assert counting_sort(arr, 8) == [1, 2, 2, 3, 3, 4, 8]


def test_stability():
    arr = [(3, 0), (1, 1), (2, 2), (1, 3), (3, 4)]
    sorted_arr = counting_sort_by_key(arr, 3, lambda x: x[0])
    assert sorted_arr == [(1, 1), (1, 3), (2, 2), (3, 0), (3, 4)]


def test_invalid_input():
    with pytest.raises(ValueError):
        counting_sort([1, 2, 10], 5)


def test_negative():
    with pytest.raises(ValueError):
        counting_sort([1, -2, 3], 5)


def test_all_same():
    arr = [5, 5, 5, 5]
    assert counting_sort(arr, 5) == [5, 5, 5, 5]
