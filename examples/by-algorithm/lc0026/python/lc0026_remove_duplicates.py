"""
LeetCode 26. Remove Duplicates from Sorted Array
链接: https://leetcode.com/problems/remove-duplicates-from-sorted-array/
难度: Easy

题目描述:
给你一个非严格递增排列的数组 nums，请你原地删除重复出现的元素，使每个元素只出现一次，
返回删除后数组的新长度。元素的相对顺序应该保持一致。

形式化规约:
  输入: nums ∈ Z^n，非递减排序
  输出: 整数 k，使得 nums[0..k) 包含原数组中所有不同元素各一次，保持相对顺序

最优解思路:
  双指针（快慢指针）：slow 指向已去重区域的下一个写入位置，fast 遍历数组。
  当 nums[fast] != nums[slow-1] 时，将 nums[fast] 复制到 nums[slow]，slow 前进。

复杂度:
  时间: O(n)
  空间: O(1)

正确性要点:
  1. 数组已排序，重复元素相邻
  2. slow 始终指向下一个待写入的去重位置
  3. 第一个元素必然保留，故 slow 从 1 开始
"""

from typing import List


class Solution:
    def removeDuplicates(self, nums: List[int]) -> int:
        """
        原地删除有序数组中的重复项，返回去重后的长度。
        时间复杂度 O(n)，空间复杂度 O(1)。
        """
        n = len(nums)
        if n == 0:
            return 0

        slow = 1
        for fast in range(1, n):
            if nums[fast] != nums[slow - 1]:
                nums[slow] = nums[fast]
                slow += 1
        return slow


def test_remove_duplicates():
    sol = Solution()

    # 示例 1
    nums1 = [1, 1, 2]
    k1 = sol.removeDuplicates(nums1)
    assert k1 == 2 and nums1[:k1] == [1, 2], f"Test 1 failed: k={k1}, nums={nums1[:k1]}"

    # 示例 2
    nums2 = [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
    k2 = sol.removeDuplicates(nums2)
    assert k2 == 5 and nums2[:k2] == [0, 1, 2, 3, 4], f"Test 2 failed: k={k2}, nums={nums2[:k2]}"

    # 边界：空数组
    assert sol.removeDuplicates([]) == 0, "Test empty failed"

    # 边界：单元素
    nums3 = [5]
    k3 = sol.removeDuplicates(nums3)
    assert k3 == 1 and nums3[:k3] == [5], f"Test single failed: k={k3}"

    # 边界：全不同
    nums4 = [1, 2, 3, 4, 5]
    k4 = sol.removeDuplicates(nums4)
    assert k4 == 5 and nums4[:k4] == [1, 2, 3, 4, 5], f"Test distinct failed"

    # 边界：全相同
    nums5 = [2, 2, 2, 2, 2]
    k5 = sol.removeDuplicates(nums5)
    assert k5 == 1 and nums5[:k5] == [2], f"Test all same failed"

    print("All tests passed for LC 26 - Remove Duplicates from Sorted Array")


if __name__ == "__main__":
    test_remove_duplicates()
