"""
LeetCode 1. Two Sum
链接: https://leetcode.com/problems/two-sum/
难度: Easy

题目描述:
给定一个整数数组 nums 和一个整数目标值 target，请你在该数组中找出和为目标值 target 的那两个整数，
并返回它们的数组下标。

你可以假设每种输入只会对应一个答案。但是，数组中同一个元素在答案里不能重复出现。
你可以按任意顺序返回答案。

形式化规约:
  输入: nums ∈ Z^n, target ∈ Z
  输出: 索引对 (i, j) 使得 nums[i] + nums[j] = target, i ≠ j

最优解思路:
  哈希表法：遍历数组，对于每个 nums[i]，查询哈希表中是否存在 target - nums[i]。
  若存在则返回结果，否则将 nums[i] 及其索引存入哈希表。

复杂度:
  时间: O(n)
  空间: O(n)

正确性要点:
  1. 哈希表的键为数值，值为索引
  2. 遍历时先查询后插入，避免同一元素被使用两次
"""

from typing import List


class Solution:
    def twoSum(self, nums: List[int], target: int) -> List[int]:
        """
        使用哈希表存储已遍历元素及其索引。
        时间复杂度 O(n)，空间复杂度 O(n)。
        """
        seen = {}  # value -> index
        for i, num in enumerate(nums):
            complement = target - num
            if complement in seen:
                return [seen[complement], i]
            seen[num] = i
        return []  # 题目保证有解，此处不会到达


def test_two_sum():
    sol = Solution()
    # 示例 1
    nums1, target1 = [2, 7, 11, 15], 9
    res1 = sol.twoSum(nums1, target1)
    assert sorted(res1) == [0, 1], f"Test 1 failed: {res1}"
    # 示例 2
    nums2, target2 = [3, 2, 4], 6
    res2 = sol.twoSum(nums2, target2)
    assert sorted(res2) == [1, 2], f"Test 2 failed: {res2}"
    # 示例 3
    nums3, target3 = [3, 3], 6
    res3 = sol.twoSum(nums3, target3)
    assert sorted(res3) == [0, 1], f"Test 3 failed: {res3}"
    # 边界: 负数
    nums4, target4 = [-1, -2, -3, -4, -5], -8
    res4 = sol.twoSum(nums4, target4)
    assert sorted(res4) == [2, 4], f"Test 4 failed: {res4}"
    print("All tests passed for LC 1 - Two Sum")


if __name__ == "__main__":
    test_two_sum()
