"""
Longest Increasing Subsequence (LIS) — Python 教学实现

对标: formal_algorithms::longest_increasing_subsequence (Rust 实现)
CLRS 4th Ed. Ex 14.4-6 / MIT 6.006 Dynamic Programming 模块

提供两种实现:
- O(n²) 动态规划（可还原序列）
- O(n log n) 二分优化（仅返回长度）
"""

from typing import List
from bisect import bisect_left


def lis_length_dp(arr: List[int]) -> int:
    """O(n²) 动态规划求 LIS 长度

    dp[i] = 以 arr[i] 结尾的最长递增子序列长度
    """
    n = len(arr)
    if n == 0:
        return 0

    dp = [1] * n
    for i in range(1, n):
        for j in range(i):
            if arr[j] < arr[i]:
                dp[i] = max(dp[i], dp[j] + 1)

    return max(dp)


def lis_dp(arr: List[int]) -> List[int]:
    """O(n²) 动态规划求 LIS 序列本身"""
    n = len(arr)
    if n == 0:
        return []

    dp = [1] * n
    prev = [-1] * n

    max_len = 1
    max_idx = 0

    for i in range(1, n):
        for j in range(i):
            if arr[j] < arr[i] and dp[j] + 1 > dp[i]:
                dp[i] = dp[j] + 1
                prev[i] = j
        if dp[i] > max_len:
            max_len = dp[i]
            max_idx = i

    # 回溯
    result = []
    cur = max_idx
    while cur != -1:
        result.append(arr[cur])
        cur = prev[cur]
    result.reverse()
    return result


def lis_length_binary(arr: List[int]) -> int:
    """O(n log n) 二分优化求 LIS 长度

    tails[k] = 长度为 k+1 的递增子序列的最小末尾元素
    """
    tails = []
    for num in arr:
        pos = bisect_left(tails, num)
        if pos == len(tails):
            tails.append(num)
        else:
            tails[pos] = num
    return len(tails)
