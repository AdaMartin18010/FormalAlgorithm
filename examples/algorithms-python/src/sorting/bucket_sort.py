"""
桶排序实现 - Python版本

桶排序假设输入数据近似均匀分布于 [0, 1) 区间。
通过将数据分桶后对各桶单独排序，期望时间复杂度为 O(n)。
"""

from typing import List, TypeVar, Callable

T = TypeVar("T")


def bucket_sort(arr: List[float]) -> None:
    """
    桶排序（浮点数版本）

    对 [0.0, 1.0) 范围内的 f64 数组进行桶排序。
    将 [0, 1) 划分为 n 个等宽桶，每个桶内使用插入排序。

    Args:
        arr: 输入浮点数数组（原地修改）

    Time: 期望 O(n)，最坏 O(n²)
    Space: O(n)
    """
    if len(arr) <= 1:
        return

    n = len(arr)
    buckets: List[List[float]] = [[] for _ in range(n)]

    for val in arr:
        bucket_index = min(int(val * n), n - 1)
        buckets[bucket_index].append(val)

    for bucket in buckets:
        _insertion_sort(bucket)

    idx = 0
    for bucket in buckets:
        for val in bucket:
            arr[idx] = val
            idx += 1


def bucket_sort_by(arr: List[T], to_unit: Callable[[T], float]) -> None:
    """
    泛型桶排序

    通过提供值到 [0, 1) 的映射函数，可以对任意类型进行桶排序。

    Args:
        arr: 输入数组（原地修改）
        to_unit: 将元素映射到 [0.0, 1.0) 的函数
    """
    if len(arr) <= 1:
        return

    n = len(arr)
    buckets: List[List[T]] = [[] for _ in range(n)]

    for item in arr:
        key = to_unit(item)
        bucket_index = min(int(key * n), n - 1)
        buckets[bucket_index].append(item)

    for bucket in buckets:
        bucket.sort()

    idx = 0
    for bucket in buckets:
        for item in bucket:
            arr[idx] = item
            idx += 1


def _insertion_sort(arr: List[float]) -> None:
    """插入排序（用于桶内排序）"""
    for i in range(1, len(arr)):
        key = arr[i]
        j = i - 1
        while j >= 0 and arr[j] > key:
            arr[j + 1] = arr[j]
            j -= 1
        arr[j + 1] = key
