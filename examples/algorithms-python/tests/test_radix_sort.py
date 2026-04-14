"""基数排序测试"""

import pytest
from src.sorting.radix_sort import radix_sort, radix_sort_by_byte


def test_empty():
    arr = []
    radix_sort(arr)
    assert arr == []


def test_single_element():
    arr = [42]
    radix_sort(arr)
    assert arr == [42]


def test_basic():
    arr = [170, 45, 75, 90, 802, 24, 2, 66]
    radix_sort(arr)
    assert arr == [2, 24, 45, 66, 75, 90, 170, 802]


def test_already_sorted():
    arr = [1, 2, 3, 4, 5]
    radix_sort(arr)
    assert arr == [1, 2, 3, 4, 5]


def test_reverse_sorted():
    arr = [987, 654, 321, 123]
    radix_sort(arr)
    assert arr == [123, 321, 654, 987]


def test_duplicates():
    arr = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
    radix_sort(arr)
    assert arr == [1, 1, 2, 3, 3, 4, 5, 5, 6, 9]


def test_negative_not_supported():
    with pytest.raises(ValueError):
        radix_sort([1, -1, 3])


def test_byte_sort():
    arr = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0x00000000]
    radix_sort_by_byte(arr)
    assert arr == [0x00000000, 0x12345678, 0xCAFEBABE, 0xDEADBEEF]


def test_large_numbers():
    arr = [1_000_000, 999_999, 1, 0, 500_000]
    radix_sort(arr)
    assert arr == [0, 1, 500_000, 999_999, 1_000_000]
