"""Tests for binary search module."""

import pytest
from src.search.binary_search import binary_search, binary_search_recursive, lower_bound, upper_bound


class TestBinarySearch:
    def test_basic(self):
        arr = [1, 3, 5, 7, 9]
        assert binary_search(arr, 5) == 2
        assert binary_search(arr, 1) == 0
        assert binary_search(arr, 9) == 4

    def test_not_found(self):
        arr = [1, 3, 5, 7, 9]
        assert binary_search(arr, 0) == -1
        assert binary_search(arr, 10) == -1
        assert binary_search(arr, 4) == -1

    def test_empty(self):
        assert binary_search([], 1) == -1

    def test_single_element(self):
        assert binary_search([5], 5) == 0
        assert binary_search([5], 3) == -1

    def test_duplicates(self):
        arr = [1, 2, 2, 2, 3]
        # Returns one of the matching indices
        idx = binary_search(arr, 2)
        assert arr[idx] == 2

    def test_recursive(self):
        arr = [1, 3, 5, 7, 9]
        assert binary_search_recursive(arr, 5) == 2
        assert binary_search_recursive(arr, 4) == -1

    def test_lower_bound(self):
        arr = [1, 3, 5, 5, 7, 9]
        assert lower_bound(arr, 5) == 2
        assert lower_bound(arr, 4) == 2
        assert lower_bound(arr, 10) == 6

    def test_upper_bound(self):
        arr = [1, 3, 5, 5, 7, 9]
        assert upper_bound(arr, 5) == 4
        assert upper_bound(arr, 4) == 2
        assert upper_bound(arr, 10) == 6

    def test_with_key(self):
        arr = [(1, "a"), (3, "b"), (5, "c"), (7, "d")]
        assert binary_search(arr, (5, "c"), key=lambda x: x[0]) == 2
        assert lower_bound(arr, (4, ""), key=lambda x: x[0]) == 2
