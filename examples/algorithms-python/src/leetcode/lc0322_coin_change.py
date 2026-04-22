"""
LeetCode 322. Coin Change
链接: https://leetcode.com/problems/coin-change/
难度: Medium

题目描述:
给你一个整数数组 coins，表示不同面额的硬币；以及一个整数 amount，表示总金额。
计算并返回可以凑成总金额所需的最少的硬币个数。如果没有任何一种硬币组合能组成总金额，返回 -1。

形式化规约:
  输入: 硬币面额数组 coins ∈ N^k，目标金额 amount ∈ N
  输出: 凑成 amount 的最少硬币数，若无法凑成则返回 -1

最优解思路:
  dp[i] 表示凑成金额 i 的最少硬币数。
  dp[i] = min_{c ∈ coins, c ≤ i} (dp[i-c] + 1)

复杂度:
  时间: O(amount × k)
  空间: O(amount)

正确性要点:
  1. 初始化 dp[0] = 0，其余为 ∞（可用 amount + 1 表示）
  2. 遍历顺序：完全背包问题，外层遍历金额，内层遍历硬币
  3. 若 dp[amount] > amount，返回 -1（表示无法凑成）
"""

from typing import List


class Solution:
    def coinChange(self, coins: List[int], amount: int) -> int:
        """
        完全背包解法。时间 O(amount * k)，空间 O(amount)。
        """
        INF = amount + 1
        dp = [INF] * (amount + 1)
        dp[0] = 0

        for i in range(1, amount + 1):
            for c in coins:
                if c <= i:
                    dp[i] = min(dp[i], dp[i - c] + 1)

        return dp[amount] if dp[amount] <= amount else -1

    def coinChangeOptimized(self, coins: List[int], amount: int) -> int:
        """
        优化版本：先遍历硬币，再遍历金额（标准完全背包写法）。
        时间与空间复杂度相同，但更贴近背包模板。
        """
        INF = amount + 1
        dp = [INF] * (amount + 1)
        dp[0] = 0

        for c in coins:
            for i in range(c, amount + 1):
                dp[i] = min(dp[i], dp[i - c] + 1)

        return dp[amount] if dp[amount] <= amount else -1


def test_coin_change():
    sol = Solution()
    # 示例 1
    assert sol.coinChange([1, 2, 5], 11) == 3, "Test 1 failed"  # 5+5+1
    # 示例 2
    assert sol.coinChange([2], 3) == -1, "Test 2 failed"
    # 示例 3
    assert sol.coinChange([1], 0) == 0, "Test 3 failed"
    # 示例 4
    assert sol.coinChange([1], 1) == 1, "Test 4 failed"
    # 示例 5
    assert sol.coinChange([1], 2) == 2, "Test 5 failed"
    # 优化版本对比
    assert sol.coinChangeOptimized([1, 2, 5], 11) == 3, "Test opt 1 failed"
    assert sol.coinChangeOptimized([2], 3) == -1, "Test opt 2 failed"
    print("All tests passed for LC 322 - Coin Change")


if __name__ == "__main__":
    test_coin_change()
