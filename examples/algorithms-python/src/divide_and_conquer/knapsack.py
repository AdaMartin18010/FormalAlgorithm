"""
0/1 Knapsack 背包问题 — Python 教学实现

对标: formal_algorithms::knapsack (Rust 实现)
CLRS 4th Ed. Ch 14.1 / MIT 6.006 Dynamic Programming 模块

核心思想:
- dp[w] = 容量为 w 时的最大价值
- 状态转移: dp[w] = max(dp[w], dp[w-weight[i]] + value[i])
"""

from typing import List, Optional, Tuple


def knapsack_01(weights: List[int], values: List[int], capacity: int) -> int:
    """0/1 背包：返回最大价值

    Args:
        weights: 每个物品的重量列表
        values: 每个物品的价值列表
        capacity: 背包容量

    Returns:
        最大总价值

    Examples:
        >>> knapsack_01([2, 3, 4, 5], [3, 4, 5, 6], 5)
        7
    """
    n = len(weights)
    if n == 0 or capacity == 0:
        return 0

    dp = [0] * (capacity + 1)
    for i in range(n):
        for w in range(capacity, weights[i] - 1, -1):
            dp[w] = max(dp[w], dp[w - weights[i]] + values[i])

    return dp[capacity]


def knapsack_01_with_selection(weights: List[int], values: List[int], capacity: int) -> Tuple[int, List[int]]:
    """0/1 背包：返回最大价值及选择的物品索引

    Returns:
        (max_value, selected_indices)
    """
    n = len(weights)
    if n == 0 or capacity == 0:
        return 0, []

    dp = [[0] * (capacity + 1) for _ in range(n + 1)]

    for i in range(1, n + 1):
        for w in range(capacity + 1):
            dp[i][w] = dp[i - 1][w]
            if w >= weights[i - 1]:
                dp[i][w] = max(dp[i][w], dp[i - 1][w - weights[i - 1]] + values[i - 1])

    # 回溯
    selected = []
    w = capacity
    for i in range(n, 0, -1):
        if dp[i][w] != dp[i - 1][w]:
            selected.append(i - 1)
            w -= weights[i - 1]
    selected.reverse()

    return dp[n][capacity], selected
