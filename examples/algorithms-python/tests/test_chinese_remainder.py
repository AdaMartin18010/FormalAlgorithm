import pytest
from src.number_theory.chinese_remainder import (
    chinese_remainder,
    chinese_remainder_iterative,
)


def test_chinese_remainder_basic():
    result = chinese_remainder([2, 3, 2], [3, 5, 7])
    assert result is not None
    x, n = result
    assert n == 105
    assert x == 23
    assert x % 3 == 2
    assert x % 5 == 3
    assert x % 7 == 2


def test_chinese_remainder_two_equations():
    result = chinese_remainder([1, 2], [3, 5])
    assert result is not None
    x, n = result
    assert n == 15
    assert x == 7


def test_chinese_remainder_single_equation():
    result = chinese_remainder([4], [7])
    assert result == (4, 7)


def test_chinese_remainder_not_coprime():
    assert chinese_remainder([1, 2], [4, 6]) is None


def test_chinese_remainder_mismatched_lengths():
    assert chinese_remainder([1, 2], [3]) is None


def test_chinese_remainder_empty():
    assert chinese_remainder([], []) is None


def test_chinese_remainder_iterative_basic():
    result = chinese_remainder_iterative([2, 3, 2], [3, 5, 7])
    assert result is not None
    x, n = result
    assert n == 105
    assert x == 23


def test_chinese_remainder_iterative_not_coprime_compatible():
    # 4 和 6 不互素，但 1 ≡ 3 (mod 2)，有解
    result = chinese_remainder_iterative([1, 3], [4, 6])
    assert result is not None
    x, n = result
    assert n == 12
    assert x % 4 == 1
    assert x % 6 == 3


def test_chinese_remainder_iterative_not_coprime_incompatible():
    # 4 和 6 不互素，且 1 ≢ 2 (mod 2)，无解
    assert chinese_remainder_iterative([1, 2], [4, 6]) is None
