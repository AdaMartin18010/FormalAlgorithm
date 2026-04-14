"""Maximum subarray problem implementations."""

from typing import List, Optional, Tuple


def max_subarray_brute_force(arr: List[int]) -> Optional[Tuple[int, int, int]]:
    """O(n^2) brute force solution."""
    if not arr:
        return None
    max_sum = arr[0]
    left = right = 0
    for i in range(len(arr)):
        s = 0
        for j in range(i, len(arr)):
            s += arr[j]
            if s > max_sum:
                max_sum = s
                left, right = i, j
    return left, right, max_sum


def max_subarray_divide_and_conquer(arr: List[int]) -> Optional[Tuple[int, int, int]]:
    """O(n log n) divide and conquer solution."""
    if not arr:
        return None

    def _cross(low: int, mid: int, high: int) -> Tuple[int, int, int]:
        left_sum = float('-inf')
        s = 0
        max_left = mid
        for i in range(mid, low - 1, -1):
            s += arr[i]
            if s > left_sum:
                left_sum = s
                max_left = i
        right_sum = float('-inf')
        s = 0
        max_right = mid + 1
        for j in range(mid + 1, high + 1):
            s += arr[j]
            if s > right_sum:
                right_sum = s
                max_right = j
        return max_left, max_right, left_sum + right_sum

    def _rec(low: int, high: int) -> Tuple[int, int, int]:
        if low == high:
            return low, high, arr[low]
        mid = (low + high) // 2
        l_low, l_high, l_sum = _rec(low, mid)
        r_low, r_high, r_sum = _rec(mid + 1, high)
        c_low, c_high, c_sum = _cross(low, mid, high)
        if l_sum >= r_sum and l_sum >= c_sum:
            return l_low, l_high, l_sum
        if r_sum >= l_sum and r_sum >= c_sum:
            return r_low, r_high, r_sum
        return c_low, c_high, c_sum

    return _rec(0, len(arr) - 1)


def max_subarray_kadane(arr: List[int]) -> Optional[Tuple[int, int, int]]:
    """O(n) Kadane's algorithm."""
    if not arr:
        return None
    max_sum = current_sum = arr[0]
    max_left = current_left = 0
    max_right = 0
    for i in range(1, len(arr)):
        if current_sum < 0:
            current_sum = arr[i]
            current_left = i
        else:
            current_sum += arr[i]
        if current_sum > max_sum:
            max_sum = current_sum
            max_left = current_left
            max_right = i
    return max_left, max_right, max_sum
