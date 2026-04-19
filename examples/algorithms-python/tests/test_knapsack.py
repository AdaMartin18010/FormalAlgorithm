"""Tests for knapsack module."""

import pytest
from src.divide_and_conquer.knapsack import knapsack_01, knapsack_01_with_selection


class TestKnapsack:
    def test_basic(self):
        weights = [2, 3, 4, 5]
        values = [3, 4, 5, 6]
        assert knapsack_01(weights, values, 5) == 7

    def test_empty(self):
        assert knapsack_01([], [], 10) == 0

    def test_zero_capacity(self):
        assert knapsack_01([1, 2, 3], [10, 20, 30], 0) == 0

    def test_with_selection(self):
        weights = [2, 3, 4, 5]
        values = [3, 4, 5, 6]
        max_value, selected = knapsack_01_with_selection(weights, values, 5)
        assert max_value == 7
        total_weight = sum(weights[i] for i in selected)
        total_value = sum(values[i] for i in selected)
        assert total_weight <= 5
        assert total_value == 7
