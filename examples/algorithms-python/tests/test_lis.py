"""Tests for LIS module."""

import pytest
from src.divide_and_conquer.lis import lis_length_dp, lis_dp, lis_length_binary


class TestLIS:
    def test_basic(self):
        arr = [10, 9, 2, 5, 3, 7, 101, 18]
        assert lis_length_dp(arr) == 4
        assert lis_length_binary(arr) == 4

    def test_empty(self):
        assert lis_length_dp([]) == 0
        assert lis_length_binary([]) == 0

    def test_increasing(self):
        arr = [1, 2, 3, 4, 5]
        assert lis_length_dp(arr) == 5
        assert lis_length_binary(arr) == 5

    def test_decreasing(self):
        arr = [5, 4, 3, 2, 1]
        assert lis_length_dp(arr) == 1
        assert lis_length_binary(arr) == 1

    def test_sequence(self):
        arr = [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
        assert lis_length_dp(arr) == 6
        assert lis_length_binary(arr) == 6

    def test_dp_returns_valid(self):
        arr = [10, 9, 2, 5, 3, 7, 101, 18]
        result = lis_dp(arr)
        assert len(result) == 4
        for i in range(1, len(result)):
            assert result[i - 1] < result[i]
