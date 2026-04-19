"""
Coin Change 硬币找零问题 — Python 教学实现

对标: formal_algorithms::coin_change (Rust 实现)
CLRS 4th Ed. Ex 14.4-5 / LeetCode 322 / 518

提供三种变体:
- 最少硬币数
- 组合数
- 返回具体组合
"""

from typing import List, Optional


def coin_change_min(coins: List[int], amount: int) -> Optional[int]:
    """返回凑成 amount 所需的最少硬币数

    Args:
        coins: 硬币面额列表（每种无限供应）
        amount: 目标金额

    Returns:
        最少硬币数，若无法凑成则返回 None

    Examples:
        >>> coin_change_min([1, 2, 5], 11)
        3
        >>> coin_change_min([2], 3)
        None
    """
    if amount == 0:
        return 0

    dp = [float('inf')] * (amount + 1)
    dp[0] = 0

    for a in range(1, amount + 1):
        for coin in coins:
            if coin <= a:
                dp[a] = min(dp[a], dp[a - coin] + 1)

    return dp[amount] if dp[amount] != float('inf') else None


def coin_change_ways(coins: List[int], amount: int) -> int:
    """返回凑成 amount 的所有不同组合方式的数量"""
    if amount == 0:
        return 1

    dp = [0] * (amount + 1)
    dp[0] = 1

    for coin in coins:
        for a in range(coin, amount + 1):
            dp[a] += dp[a - coin]

    return dp[amount]
