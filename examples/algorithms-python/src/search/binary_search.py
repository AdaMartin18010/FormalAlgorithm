"""Binary search implementation.

Provides iterative and recursive variants for finding elements in sorted sequences.
Time complexity: O(log n), Space complexity: O(1) iterative / O(log n) recursive.
"""

from typing import TypeVar, Optional, Callable, Sequence

T = TypeVar("T")


def binary_search(arr: Sequence[T], target: T,
                  key: Optional[Callable[[T], any]] = None) -> int:
    """Return the index of target in sorted arr, or -1 if not found.

    Args:
        arr: Sorted sequence supporting indexing and length.
        target: Value to search for.
        key: Optional key extraction function.

    Returns:
        Index of target if found, otherwise -1.

    Examples:
        >>> binary_search([1, 3, 5, 7, 9], 5)
        2
        >>> binary_search([1, 3, 5, 7, 9], 4)
        -1
    """
    left, right = 0, len(arr) - 1
    get_key = key if key else lambda x: x
    target_key = get_key(target)
    while left <= right:
        mid = (left + right) // 2
        mid_key = get_key(arr[mid])
        if mid_key == target_key:
            return mid
        elif mid_key < target_key:
            left = mid + 1
        else:
            right = mid - 1
    return -1


def binary_search_recursive(arr: Sequence[T], target: T,
                            key: Optional[Callable[[T], any]] = None) -> int:
    """Recursive variant of binary search.

    Args:
        arr: Sorted sequence.
        target: Value to search for.
        key: Optional key extraction function.

    Returns:
        Index of target if found, otherwise -1.
    """
    def _search(left: int, right: int) -> int:
        if left > right:
            return -1
        mid = (left + right) // 2
        get_key = key if key else lambda x: x
        mid_key = get_key(arr[mid])
        target_key = get_key(target)
        if mid_key == target_key:
            return mid
        elif mid_key < target_key:
            return _search(mid + 1, right)
        else:
            return _search(left, mid - 1)
    return _search(0, len(arr) - 1)


def lower_bound(arr: Sequence[T], target: T,
                key: Optional[Callable[[T], any]] = None) -> int:
    """Return the first index i such that arr[i] >= target.

    If all elements are < target, returns len(arr).

    Args:
        arr: Sorted sequence.
        target: Value to compare against.
        key: Optional key extraction function.

    Returns:
        Lower bound index in [0, len(arr)].
    """
    left, right = 0, len(arr)
    get_key = key if key else lambda x: x
    target_key = get_key(target)
    while left < right:
        mid = (left + right) // 2
        if get_key(arr[mid]) < target_key:
            left = mid + 1
        else:
            right = mid
    return left


def upper_bound(arr: Sequence[T], target: T,
                key: Optional[Callable[[T], any]] = None) -> int:
    """Return the first index i such that arr[i] > target.

    If all elements are <= target, returns len(arr).

    Args:
        arr: Sorted sequence.
        target: Value to compare against.
        key: Optional key extraction function.

    Returns:
        Upper bound index in [0, len(arr)].
    """
    left, right = 0, len(arr)
    get_key = key if key else lambda x: x
    target_key = get_key(target)
    while left < right:
        mid = (left + right) // 2
        if get_key(arr[mid]) <= target_key:
            left = mid + 1
        else:
            right = mid
    return left
