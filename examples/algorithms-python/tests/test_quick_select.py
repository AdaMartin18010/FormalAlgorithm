"""快速选择与中位数测试"""

import pytest
from src.sorting.quick_select import (
    quick_select,
    median_of_medians_select,
    find_median,
    find_min,
    find_max,
)


def test_quick_select_basic():
    arr = [7, 10, 4, 3, 20, 15]
    assert quick_select(arr.copy(), 0) == 3
    assert quick_select(arr.copy(), 2) == 7
    assert quick_select(arr.copy(), 5) == 20


def test_quick_select_single():
    assert quick_select([42], 0) == 42


def test_quick_select_duplicates():
    arr = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
    assert quick_select(arr.copy(), 0) == 1
    assert quick_select(arr.copy(), 9) == 9


def test_quick_select_error():
    with pytest.raises(ValueError):
        quick_select([1, 2, 3], 10)


def test_median_of_medians():
    arr = [7, 10, 4, 3, 20, 15, 1, 8, 12]
    assert median_of_medians_select(arr.copy(), 0) == 1
    assert median_of_medians_select(arr.copy(), 4) == 8
    assert median_of_medians_select(arr.copy(), 8) == 20


def test_find_median():
    assert find_median([7, 10, 4, 3, 20]) == 7
    assert find_median([7, 10, 4, 3, 20, 15]) == 10


def test_find_min_max():
    arr = [7, 10, 4, 3, 20]
    assert find_min(arr.copy()) == 3
    assert find_max(arr.copy()) == 20


def test_large_array():
    arr = list(range(999, -1, -1))
    for i in range(1000):
        assert quick_select(arr.copy(), i) == i


def test_mom_large_array():
    arr = list(range(99, -1, -1))
    for i in range(100):
        assert median_of_medians_select(arr.copy(), i) == i
