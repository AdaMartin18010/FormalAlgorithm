"""
计数排序实现 - Python版本

计数排序是一种非比较排序算法，适用于整数范围已知且不大的场景。
时间复杂度 O(n + k)，当 k = O(n) 时为线性时间。
"""

from typing import List, TypeVar, Callable

T = TypeVar("T")


def counting_sort(arr: List[int], max_val: int) -> List[int]:
    """
    稳定计数排序

    对输入数组进行稳定计数排序，返回新的有序数组。
    假设所有元素均为 [0, max_val] 范围内的非负整数。

    Args:
        arr: 输入整数数组
        max_val: 数组中元素的最大值

    Returns:
        排序后的新数组

    Raises:
        ValueError: 若数组中存在大于 max_val 的元素

    Time: O(n + k)
    Space: O(n + k)
    """
    if not arr:
        return []

    if any(v > max_val for v in arr):
        raise ValueError("Array contains element greater than max_val")
    if any(v < 0 for v in arr):
        raise ValueError("Array contains negative element")

    # 1. 计数
    count = [0] * (max_val + 1)
    for val in arr:
        count[val] += 1

    # 2. 累加: count[i] 表示 <= i 的元素个数
    for i in range(1, max_val + 1):
        count[i] += count[i - 1]

    # 3. 放置: 逆序遍历保持稳定性
    output = [0] * len(arr)
    for val in reversed(arr):
        output[count[val] - 1] = val
        count[val] -= 1

    return output


def counting_sort_by_key(
    arr: List[T], max_key: int, key_fn: Callable[[T], int]
) -> List[T]:
    """
    泛型计数排序（支持可映射为整数的键）

    Args:
        arr: 输入数组
        max_key: 键的最大值
        key_fn: 键提取函数

    Returns:
        排序后的新数组
    """
    if not arr:
        return []

    if any(key_fn(v) > max_key for v in arr):
        raise ValueError("Key exceeds max_key")
    if any(key_fn(v) < 0 for v in arr):
        raise ValueError("Key contains negative value")

    count = [0] * (max_key + 1)
    for item in arr:
        count[key_fn(item)] += 1

    for i in range(1, max_key + 1):
        count[i] += count[i - 1]

    output = [None] * len(arr)  # type: ignore[list-item]
    for item in reversed(arr):
        k = key_fn(item)
        output[count[k] - 1] = item
        count[k] -= 1

    return output  # type: ignore[return-value]
