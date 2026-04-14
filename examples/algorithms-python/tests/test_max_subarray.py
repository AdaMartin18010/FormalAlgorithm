from src.divide_and_conquer.max_subarray import (
    max_subarray_brute_force,
    max_subarray_divide_and_conquer,
    max_subarray_kadane,
)


def _test_all(arr, expected_sum, expected_slice):
    for func in [max_subarray_brute_force, max_subarray_divide_and_conquer, max_subarray_kadane]:
        result = func(arr)
        assert result is not None
        l, r, s = result
        assert s == expected_sum
        assert arr[l : r + 1] == expected_slice


def test_clrs_example():
    arr = [13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7]
    _test_all(arr, 43, [18, 20, -7, 12])


def test_all_negative():
    arr = [-5, -2, -8, -1, -9]
    _test_all(arr, -1, [-1])


def test_single_element():
    _test_all([42], 42, [42])


def test_empty():
    assert max_subarray_kadane([]) is None
    assert max_subarray_brute_force([]) is None
    assert max_subarray_divide_and_conquer([]) is None
