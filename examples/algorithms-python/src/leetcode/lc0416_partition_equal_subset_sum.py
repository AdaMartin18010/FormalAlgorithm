"""LeetCode 416. 分割等和子集 / Partition Equal Subset Sum — Python 实现

给你一个只包含正整数的非空数组 nums 。请你判断是否可以将这个数组分割成两个子集，
使得两个子集的元素和相等。

题目链接: https://leetcode.com/problems/partition-equal-subset-sum/
难度: Medium

对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.5
"""

from typing import List


def can_partition(nums: List[int]) -> bool:
    """判断数组是否能被分割成两个和相等的子集。

    前置条件 (Pre):
        - nums 为正整数数组，长度范围 [1, 200]，元素范围 [1, 100]。

    后置条件 (Post):
        - 返回 True 当且仅当数组可被均分为两个和相等的子集。

    核心思路:
        0/1 背包判定问题。
        设 total = sum(nums)。若 total 为奇数，直接返回 False。
        否则目标为：能否从 nums 中选出一个子集，使其和为 target = total // 2。

        动态规划：设 dp[w] 表示能否凑出重量 w。
        状态转移：dp[w] = dp[w] or dp[w - nums[i]] （逆序遍历）
        初始条件：dp[0] = True（空集和为 0）

        逆序遍历关键：0/1 背包中每个物品只能选一次。
        若正序遍历，dp[w - nums[i]] 可能已被当前物品更新，导致重复选择（变成完全背包）。

    复杂度:
        时间复杂度: O(n * target) — target = sum(nums) // 2。
        空间复杂度: O(target) — 一维布尔数组。

    证明要点:
        - 最优子结构：前 i 个物品能凑出 w，当且仅当不选第 i 个时已能凑出 w，
          或选第 i 个且前 i-1 个能凑出 w - nums[i]。
        - 无后效性：dp[w] 只依赖于更小的重量状态。
        - 逆序正确性：逆序保证在更新 dp[w] 时，dp[w - nums[i]] 仍是前 i-1 个物品的状态，
          确保每个数字最多被选一次。
        - 归纳证明：对物品数量归纳，基例 dp[0] = True 正确，归纳步骤由引理保证。

    Args:
        nums: 正整数数组。

    Returns:
        若能均分返回 True，否则返回 False。
    """
    total = sum(nums)
    if total % 2 != 0:
        return False

    target = total // 2
    dp = [False] * (target + 1)
    dp[0] = True

    for num in nums:
        # 逆序遍历：0/1 背包核心技巧
        for w in range(target, num - 1, -1):
            dp[w] = dp[w] or dp[w - num]
        # 提前终止
        if dp[target]:
            return True

    return dp[target]


if __name__ == "__main__":
    # LeetCode 官方示例
    assert can_partition([1, 5, 11, 5]) is True, "Example 1 failed"  # [1,5,5] vs [11]
    assert can_partition([1, 2, 3, 5]) is False, "Example 2 failed"

    # 边界条件
    assert can_partition([1]) is False, "Single element"
    assert can_partition([2, 2]) is True, "Two equal elements"
    assert can_partition([1, 2, 4]) is False, "Odd sum"
    assert can_partition([1, 1, 1, 1, 1, 1, 1, 1]) is True, "All ones"

    # 额外测试
    assert can_partition([3, 3, 3, 4, 5]) is True, "Complex case"
    assert can_partition([100] * 8 + [1]) is False, "Impossible"

    print("All tests passed.")
