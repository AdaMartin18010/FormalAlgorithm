"""
LeetCode 198. House Robber
https://leetcode.com/problems/house-robber/

Problem: Given an integer array nums representing money in each house,
return the maximum amount you can rob without alerting police.
Cannot rob two adjacent houses.

Formal specification:
- Pre: nums.length >= 0
- Post: result = max sum of non-adjacent elements

Algorithm: DP with optimal substructure.
dp[i] = max money from houses[0..i].
Recurrence: dp[i] = max(dp[i-1], dp[i-2] + nums[i]).

Proof sketch (by induction):
Base: i=0 → dp[0]=nums[0]; i=1 → dp[1]=max(nums[0], nums[1]).
Inductive step: For house i, either rob it (then i-1 cannot be robbed,
so add nums[i] to dp[i-2]) or skip it (take dp[i-1]).

Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
Lean proof: examples/lean_proofs/leetcode/lc0198_house_robber.lean
"""

from typing import List


def rob(nums: List[int]) -> int:
    """Space-optimized DP: O(n) time, O(1) space."""
    n = len(nums)
    if n == 0:
        return 0
    if n == 1:
        return nums[0]

    prev2 = nums[0]
    prev1 = max(nums[0], nums[1])

    for i in range(2, n):
        curr = max(prev1, prev2 + nums[i])
        prev2, prev1 = prev1, curr

    return prev1


def rob_with_states(nums: List[int]) -> int:
    """State-machine DP: track (rob, not_rob) for each house."""
    rob_prev, not_rob_prev = 0, 0

    for money in nums:
        rob_curr = not_rob_prev + money
        not_rob_curr = max(rob_prev, not_rob_prev)
        rob_prev, not_rob_prev = rob_curr, not_rob_curr

    return max(rob_prev, not_rob_prev)


if __name__ == "__main__":
    assert rob([1, 2, 3, 1]) == 4  # 1 + 3
    assert rob([2, 7, 9, 3, 1]) == 12  # 2 + 9 + 1
    assert rob([]) == 0
    assert rob([5]) == 5
    assert rob([3, 5]) == 5

    assert rob_with_states([1, 2, 3, 1]) == 4
    assert rob_with_states([2, 7, 9, 3, 1]) == 12

    print("All tests passed for LC 198.")
