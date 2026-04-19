"""Tests for insertion_sort module."""

import pytest
from src.sorting.insertion_sort import insertion_sort, insertion_sort_binary


class TestInsertionSort:
    def test_empty(self):
        arr = []
        insertion_sort(arr)
        assert arr == []

    def test_single_element(self):
        arr = [42]
        insertion_sort(arr)
        assert arr == [42]

    def test_already_sorted(self):
        arr = [1, 2, 3, 4, 5]
        insertion_sort(arr)
        assert arr == [1, 2, 3, 4, 5]

    def test_reverse_sorted(self):
        arr = [5, 4, 3, 2, 1]
        insertion_sort(arr)
        assert arr == [1, 2, 3, 4, 5]

    def test_random(self):
        arr = [64, 34, 25, 12, 22, 11, 90]
        insertion_sort(arr)
        assert arr == [11, 12, 22, 25, 34, 64, 90]

    def test_stability(self):
        arr = [(3, 0), (1, 1), (2, 2), (1, 3)]
        insertion_sort(arr, key=lambda x: x[0])
        assert arr[0] == (1, 1)
        assert arr[1] == (1, 3)

    def test_binary_version(self):
        arr = [64, 34, 25, 12, 22, 11, 90]
        insertion_sort_binary(arr)
        assert arr == [11, 12, 22, 25, 34, 64, 90]
