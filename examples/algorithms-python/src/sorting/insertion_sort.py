"""
Insertion Sort 插入排序 — Python 教学实现

对标: formal_algorithms::insertion_sort (Rust 实现)
CLRS 4th Ed. Ch 2.1 / MIT 6.006 核心教学内容

核心性质:
- 时间复杂度: 最坏 O(n²), 最好 O(n), 平均 O(n²)
- 空间复杂度: O(1)
- 稳定性: 稳定排序
"""


def insertion_sort(arr: list, key=None) -> None:
    """原地插入排序

    Args:
        arr: 待排序的可变序列，元素需支持比较操作
        key: 可选的键提取函数

    Examples:
        >>> data = [64, 34, 25, 12, 22, 11, 90]
        >>> insertion_sort(data)
        >>> data
        [11, 12, 22, 25, 34, 64, 90]
    """
    for i in range(1, len(arr)):
        cur = arr[i]
        cur_key = key(cur) if key else cur
        j = i - 1
        while j >= 0 and (key(arr[j]) if key else arr[j]) > cur_key:
            arr[j + 1] = arr[j]
            j -= 1
        arr[j + 1] = cur


def insertion_sort_binary(arr: list) -> None:
    """二分查找优化的插入排序

    用二分查找确定插入位置，减少比较次数。
    比较复杂度: O(n log n)；移动复杂度仍为 O(n²)。
    """
    from bisect import bisect_left

    for i in range(1, len(arr)):
        key = arr[i]
        pos = bisect_left(arr, key, 0, i)
        arr[pos + 1:i + 1] = arr[pos:i]
        arr[pos] = key
