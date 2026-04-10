"""
排序算法实现 - Python版本
包含：快速排序、归并排序、堆排序、计数排序、基数排序
"""

from typing import List, TypeVar
import random

T = TypeVar('T')


def quick_sort(arr: List[T]) -> List[T]:
    """
    快速排序 - 非原地版本
    时间: O(n log n)平均, O(n^2)最坏
    空间: O(n)用于输出
    """
    if len(arr) <= 1:
        return arr[:]
    
    pivot = arr[len(arr) // 2]
    left = [x for x in arr if x < pivot]
    middle = [x for x in arr if x == pivot]
    right = [x for x in arr if x > pivot]
    
    return quick_sort(left) + middle + quick_sort(right)


def quick_sort_inplace(arr: List[T], low: int = 0, high: int = None) -> None:
    """
    快速排序 - 原地版本
    """
    if high is None:
        high = len(arr) - 1
    
    if low < high:
        pivot_index = _partition(arr, low, high)
        quick_sort_inplace(arr, low, pivot_index - 1)
        quick_sort_inplace(arr, pivot_index + 1, high)


def _partition(arr: List[T], low: int, high: int) -> int:
    """快速排序的分区函数"""
    pivot = arr[high]
    i = low - 1
    
    for j in range(low, high):
        if arr[j] <= pivot:
            i += 1
            arr[i], arr[j] = arr[j], arr[i]
    
    arr[i + 1], arr[high] = arr[high], arr[i + 1]
    return i + 1


def merge_sort(arr: List[T]) -> List[T]:
    """
    归并排序 - 稳定排序
    时间: O(n log n)
    空间: O(n)
    """
    if len(arr) <= 1:
        return arr[:]
    
    mid = len(arr) // 2
    left = merge_sort(arr[:mid])
    right = merge_sort(arr[mid:])
    
    return _merge(left, right)


def _merge(left: List[T], right: List[T]) -> List[T]:
    """合并两个有序数组"""
    result = []
    i = j = 0
    
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    
    result.extend(left[i:])
    result.extend(right[j:])
    return result


def heap_sort(arr: List[T]) -> None:
    """
    堆排序 - 原地排序
    时间: O(n log n)
    空间: O(1)
    """
    n = len(arr)
    
    # 建堆
    for i in range(n // 2 - 1, -1, -1):
        _heapify(arr, n, i)
    
    # 提取元素
    for i in range(n - 1, 0, -1):
        arr[0], arr[i] = arr[i], arr[0]
        _heapify(arr, i, 0)


def _heapify(arr: List[T], heap_size: int, root: int) -> None:
    """维护堆性质"""
    largest = root
    left = 2 * root + 1
    right = 2 * root + 2
    
    if left < heap_size and arr[left] > arr[largest]:
        largest = left
    
    if right < heap_size and arr[right] > arr[largest]:
        largest = right
    
    if largest != root:
        arr[root], arr[largest] = arr[largest], arr[root]
        _heapify(arr, heap_size, largest)


def counting_sort(arr: List[int], max_val: int) -> List[int]:
    """
    计数排序
    时间: O(n + k)
    空间: O(k)
    适用于: 整数，范围已知
    """
    count = [0] * (max_val + 1)
    
    # 计数
    for num in arr:
        count[num] += 1
    
    # 输出
    result = []
    for i, c in enumerate(count):
        result.extend([i] * c)
    
    return result


def radix_sort(arr: List[int]) -> None:
    """
    基数排序
    时间: O(nk)
    适用于: 固定位数整数
    """
    if not arr:
        return
    
    max_val = max(abs(x) for x in arr)
    exp = 1
    
    while max_val // exp > 0:
        _counting_sort_by_digit(arr, exp)
        exp *= 10


def _counting_sort_by_digit(arr: List[int], exp: int) -> None:
    """按特定位进行计数排序"""
    n = len(arr)
    output = [0] * n
    count = [0] * 10
    
    # 计数
    for num in arr:
        digit = (num // exp) % 10
        count[digit] += 1
    
    # 累加
    for i in range(1, 10):
        count[i] += count[i - 1]
    
    # 输出（保持稳定性）
    for i in range(n - 1, -1, -1):
        digit = (arr[i] // exp) % 10
        output[count[digit] - 1] = arr[i]
        count[digit] -= 1
    
    # 复制回原数组
    for i in range(n):
        arr[i] = output[i]


def insertion_sort(arr: List[T]) -> None:
    """
    插入排序
    时间: O(n^2)
    适用于: 小数组
    """
    for i in range(1, len(arr)):
        key = arr[i]
        j = i - 1
        while j >= 0 and arr[j] > key:
            arr[j + 1] = arr[j]
            j -= 1
        arr[j + 1] = key


def tim_sort(arr: List[T]) -> None:
    """
    Timsort - Python内置排序算法
    时间: O(n log n)
    空间: O(n)
    特点: 归并排序 + 插入排序的混合
    """
    # 实际使用内置排序，它使用Timsort
    arr.sort()


if __name__ == "__main__":
    # 测试各种排序算法
    test_arr = [3, 6, 8, 10, 1, 2, 1]
    print(f"Original: {test_arr}")
    print(f"Quick sort: {quick_sort(test_arr)}")
    
    arr2 = test_arr.copy()
    quick_sort_inplace(arr2)
    print(f"Quick sort (inplace): {arr2}")
    
    print(f"Merge sort: {merge_sort(test_arr)}")
    
    arr3 = test_arr.copy()
    heap_sort(arr3)
    print(f"Heap sort: {arr3}")
    
    int_arr = [4, 2, 2, 8, 3, 3, 1]
    print(f"Counting sort: {counting_sort(int_arr, 8)}")
    
    radix_arr = [170, 45, 75, 90, 802, 24, 2, 66]
    radix_sort(radix_arr)
    print(f"Radix sort: {radix_arr}")
