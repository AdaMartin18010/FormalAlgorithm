"""LeetCode 300. 最长递增子序列 / Longest Increasing Subsequence — Python 实现

给你一个整数数组 nums，找到其中最长严格递增子序列的长度。

子序列是由数组派生而来的序列，删除（或不删除）数组中的元素而不改变其余元素的顺序。

题目链接: https://leetcode.com/problems/longest-increasing-subsequence/
难度: Medium

对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.3
"""

from typing import List
import bisect


def length_of_lis_dp(nums: List[int]) -> int:
    """最长递增子序列 — O(n^2) 标准动态规划实现。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [1, 2500]。

    后置条件 (Post):
        - 返回最长严格递增子序列的长度。

    核心思路:
        动态规划：设 dp[i] 为以 nums[i] 结尾的最长递增子序列长度。
        状态转移：dp[i] = max{dp[j] + 1 | j < i 且 nums[j] < nums[i]}
        初始条件：dp[i] = 1（每个元素自身构成长度为 1 的递增子序列）
        答案：max(dp)

    复杂度:
        时间复杂度: O(n^2) — 双重循环。
        空间复杂度: O(n) — dp 数组。

    证明要点:
        - 最优子结构：以 nums[i] 结尾的最长递增子序列，其倒数第二个元素
          必为某个 nums[j] (j < i, nums[j] < nums[i])，且前缀必为以 nums[j]
          结尾的最长递增子序列。若不然，可替换为更长的前缀，矛盾。
        - 无后效性：dp[i] 只依赖于 j < i 的 dp[j]。

    Args:
        nums: 整数数组。

    Returns:
        最长严格递增子序列的长度。
    """
    n = len(nums)
    if n == 0:
        return 0

    dp = [1] * n
    max_len = 1

    for i in range(1, n):
        for j in range(i):
            if nums[j] < nums[i]:
                dp[i] = max(dp[i], dp[j] + 1)
        max_len = max(max_len, dp[i])

    return max_len


def length_of_lis_binary(nums: List[int]) -> int:
    """最长递增子序列 — O(n log n) 二分优化实现。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [1, 2500]。

    后置条件 (Post):
        - 返回最长严格递增子序列的长度。

    核心思路:
        维护数组 tails，其中 tails[k] 表示长度为 k+1 的递增子序列的最小末尾元素。
        tails 保持严格递增，可用 bisect_left 进行二分查找。
        对每个 num：
          - 若 num 大于 tails 末尾，追加到 tails（发现更长的子序列）
          - 否则用 num 替换 tails 中第一个 >= num 的位置（维护最小末尾）

    复杂度:
        时间复杂度: O(n log n) — 每个元素二分查找。
        空间复杂度: O(n) — tails 数组（最坏情况）。

    证明要点:
        - tails 单调性：tails[k] < tails[k+1] 恒成立。若否，则存在长度为 k+2
          的递增子序列其末尾元素 <= tails[k]，去掉最后一个元素可得更短的最优末尾，
          与 tails[k] 的定义矛盾。
        - 长度不变性：tails 的长度始终等于当前找到的最长递增子序列长度。
          因为 tails 中每个值都对应一个真实存在的递增子序列（构造过程保证），
          且只要存在长度为 L 的递增子序列，tails[L-1] 就必然有定义。
        - 贪心替换的正确性：用更小的末尾元素替换，为后续元素的接入创造更多机会，
          不会降低最终可达到的最大长度。

    Args:
        nums: 整数数组。

    Returns:
        最长严格递增子序列的长度。
    """
    tails: List[int] = []

    for num in nums:
        pos = bisect.bisect_left(tails, num)
        if pos == len(tails):
            tails.append(num)
        else:
            tails[pos] = num

    return len(tails)


if __name__ == "__main__":
    # LeetCode 官方示例
    nums1 = [10, 9, 2, 5, 3, 7, 101, 18]
    assert length_of_lis_dp(nums1.copy()) == 4, "Example 1 DP failed"
    assert length_of_lis_binary(nums1) == 4, "Example 1 binary failed"  # [2, 3, 7, 101]

    nums2 = [0, 1, 0, 3, 2, 3]
    assert length_of_lis_dp(nums2.copy()) == 4, "Example 2 DP failed"
    assert length_of_lis_binary(nums2) == 4, "Example 2 binary failed"  # [0, 1, 2, 3]

    nums3 = [7, 7, 7, 7, 7, 7, 7]
    assert length_of_lis_dp(nums3.copy()) == 1, "Example 3 DP failed"
    assert length_of_lis_binary(nums3) == 1, "Example 3 binary failed"

    # 边界条件
    assert length_of_lis_dp([1]) == 1, "Single element DP"
    assert length_of_lis_binary([1]) == 1, "Single element binary"
    assert length_of_lis_dp([5, 4, 3, 2, 1]) == 1, "Decreasing DP"
    assert length_of_lis_binary([5, 4, 3, 2, 1]) == 1, "Decreasing binary"
    assert length_of_lis_dp([1, 2, 3, 4, 5]) == 5, "Increasing DP"
    assert length_of_lis_binary([1, 2, 3, 4, 5]) == 5, "Increasing binary"

    # 验证两种方法结果一致
    test_cases = [
        [10, 9, 2, 5, 3, 7, 101, 18],
        [0, 1, 0, 3, 2, 3],
        [7, 7, 7, 7, 7],
        [1, 3, 6, 7, 9, 4, 10, 5, 6],
        [3, 1, 2, 1, 8, 5, 6],
    ]
    for nums in test_cases:
        dp_result = length_of_lis_dp(nums.copy())
        binary_result = length_of_lis_binary(nums)
        assert dp_result == binary_result, f"Mismatch: dp={dp_result}, binary={binary_result}"

    print("All tests passed.")
