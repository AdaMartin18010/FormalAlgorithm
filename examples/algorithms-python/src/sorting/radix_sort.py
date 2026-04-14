"""
基数排序实现 - Python版本

基数排序是一种非比较排序算法，通过逐位稳定排序实现整体有序。
适用于整数排序，特别是固定位数的整数。
"""

from typing import List


def radix_sort(arr: List[int]) -> None:
    """
    LSD (最低位优先) 基数排序

    对非负整数数组进行原地基数排序，按十进制位逐位排序。
    使用稳定的计数排序作为子程序。

    Args:
        arr: 输入整数数组（原地修改）

    Time: O(d(n + k))，d 为最大位数，k 为基数
    Space: O(n + k)
    """
    if len(arr) <= 1:
        return

    if any(v < 0 for v in arr):
        raise ValueError("Negative numbers are not supported")

    max_val = max(arr)
    exp = 1

    while max_val // exp > 0:
        _counting_sort_by_digit(arr, exp)
        exp *= 10


def _counting_sort_by_digit(arr: List[int], exp: int) -> None:
    """按特定位进行稳定计数排序"""
    n = len(arr)
    output = [0] * n
    count = [0] * 10

    for num in arr:
        digit = (num // exp) % 10
        count[digit] += 1

    for i in range(1, 10):
        count[i] += count[i - 1]

    for i in range(n - 1, -1, -1):
        digit = (arr[i] // exp) % 10
        output[count[digit] - 1] = arr[i]
        count[digit] -= 1

    for i in range(n):
        arr[i] = output[i]


def radix_sort_by_byte(arr: List[int]) -> None:
    """
    二进制基数排序（按字节排序）

    将 32 位无符号整数按 8 位一组（共 4 字节）进行基数排序。
    这种方法使用 k=256 的计数数组，更适合 CPU 缓存。

    Args:
        arr: 输入整数数组（原地修改，元素必须在 0~2^32-1 范围内）
    """
    if len(arr) <= 1:
        return

    for shift in range(0, 32, 8):
        _counting_sort_by_byte(arr, shift)


def _counting_sort_by_byte(arr: List[int], shift: int) -> None:
    """按特定字节进行稳定计数排序"""
    n = len(arr)
    output = [0] * n
    count = [0] * 256

    for num in arr:
        byte_val = (num >> shift) & 0xFF
        count[byte_val] += 1

    for i in range(1, 256):
        count[i] += count[i - 1]

    for i in range(n - 1, -1, -1):
        byte_val = (arr[i] >> shift) & 0xFF
        output[count[byte_val] - 1] = arr[i]
        count[byte_val] -= 1

    for i in range(n):
        arr[i] = output[i]
