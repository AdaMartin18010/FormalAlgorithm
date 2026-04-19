"""Tests for coin_change module."""

import pytest
from src.divide_and_conquer.coin_change import coin_change_min, coin_change_ways


class TestCoinChange:
    def test_min_basic(self):
        assert coin_change_min([1, 2, 5], 11) == 3
        assert coin_change_min([1, 2, 5], 3) == 2

    def test_min_impossible(self):
        assert coin_change_min([2, 5], 3) is None

    def test_min_zero(self):
        assert coin_change_min([1, 2, 5], 0) == 0

    def test_ways_basic(self):
        assert coin_change_ways([1, 2, 5], 5) == 4

    def test_ways_zero(self):
        assert coin_change_ways([1, 2, 5], 0) == 1
