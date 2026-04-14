"""
快速选择与中位数算法实现 - Python版本

提供 QuickSelect 和 Median of Medians 两种线性时间选择算法。
用于查找数组中第 k 小（或第 k 大）的元素。
"""

from typing import List, TypeVar

T = TypeVar("T")


def quick_select(arr: List[T], k: int) -> T:
    """
    QuickSelect - 查找第 k 小的元素（0-based 索引）

    平均时间复杂度 O(n)，最坏情况 O(n²)。
    该实现会修改输入数组。

    Args:
        arr: 输入数组（会被修改）
        k: 要查找的元素的排名（0-based，0 表示最小值）

    Returns:
        第 k 小的元素

    Raises:
        ValueError: 若 k 超出范围

    Time: 期望 O(n)
    Space: O(1) 辅助空间
    """
    if not arr:
        raise ValueError("Array is empty")
    if k < 0 or k >= len(arr):
        raise ValueError("k is out of bounds")

    return _quick_select_internal(arr, k)


def _quick_select_internal(arr: List[T], k: int) -> T:
    if len(arr) == 1:
        return arr[0]

    pivot_index = _partition(arr)

    if k == pivot_index:
        return arr[pivot_index]
    elif k < pivot_index:
        return _quick_select_internal(arr[:pivot_index], k)
    else:
        return _quick_select_internal(arr[pivot_index + 1 :], k - pivot_index - 1)


def _partition(arr: List[T]) -> int:
    """三数取中分区方案"""
    n = len(arr)
    mid = n // 2
    last = n - 1

    # 三数取中
    if arr[mid] < arr[0]:
        arr[0], arr[mid] = arr[mid], arr[0]
    if arr[last] < arr[0]:
        arr[0], arr[last] = arr[last], arr[0]
    if arr[mid] < arr[last]:
        arr[mid], arr[last] = arr[last], arr[mid]

    pivot = arr[last]
    i = 0
    for j in range(last):
        if arr[j] <= pivot:
            arr[i], arr[j] = arr[j], arr[i]
            i += 1

    arr[i], arr[last] = arr[last], arr[i]
    return i


def median_of_medians_select(arr: List[T], k: int) -> T:
    """
    Median of Medians - 确定性线性时间选择

    最坏情况下时间复杂度为 O(n)，但常数因子较大。

    Args:
        arr: 输入数组（会被修改）
        k: 要查找的元素的排名（0-based）

    Returns:
        第 k 小的元素
    """
    if not arr:
        raise ValueError("Array is empty")
    if k < 0 or k >= len(arr):
        raise ValueError("k is out of bounds")

    return _mom_select_internal(arr, k)


def _mom_select_internal(arr: List[T], k: int) -> T:
    if len(arr) <= 5:
        arr.sort()
        return arr[k]

    # 1. 分成每组 5 个，找出中位数
    chunks = [arr[i : i + 5] for i in range(0, len(arr), 5)]
    medians = []
    for chunk in chunks:
        chunk.sort()
        medians.append(chunk[len(chunk) // 2])

    # 2. 递归找出中位数的中位数
    pivot = _mom_select_internal(medians, len(medians) // 2)

    # 3. 用 pivot 分区
    lt = [x for x in arr if x < pivot]
    eq = [x for x in arr if x == pivot]
    gt = [x for x in arr if x > pivot]

    if k < len(lt):
        return _mom_select_internal(lt, k)
    elif k < len(lt) + len(eq):
        return eq[0]
    else:
        return _mom_select_internal(gt, k - len(lt) - len(eq))


def find_median(arr: List[T]) -> T:
    """查找中位数（若长度为偶数，返回下中位数）"""
    return quick_select(arr, len(arr) // 2)


def find_min(arr: List[T]) -> T:
    """查找最小值"""
    return quick_select(arr, 0)


def find_max(arr: List[T]) -> T:
    """查找最大值"""
    return quick_select(arr, len(arr) - 1)
