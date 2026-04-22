"""LeetCode 4. 寻找两个正序数组的中位数 — Python 实现

给定两个大小分别为 m 和 n 的正序（从小到大）数组 nums1 和 nums2。
请你找出并返回这两个正序数组的中位数。

算法的时间复杂度应该为 O(log (m+n))。

对标: LeetCode 4 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
"""

from typing import List


def find_median_sorted_arrays(nums1: List[int], nums2: List[int]) -> float:
    """寻找两个正序数组的中位数。

    前置条件 (Pre):
        - nums1 和 nums2 各自按非降序排列。
        - m + n >= 1。

    后置条件 (Post):
        - 返回两个数组合并后的中位数。

    核心思路:
        二分/分治混合：在较短的数组上进行二分查找分割点。
        设将 nums1 在位置 i 处分割，nums2 在位置 j 处分割，满足 i + j = (m + n + 1) / 2。
        要求：nums1[i-1] <= nums2[j] 且 nums2[j-1] <= nums1[i]。

    复杂度:
        时间复杂度: O(log(min(m, n))) — 在较短数组上二分。
        空间复杂度: O(1) — 仅使用常数额外变量。

    证明要点:
        - 引理：若分割满足左右平衡且左半最大值 <= 右半最小值，则中位数可正确计算。
        - 引理：二分搜索空间具有单调性，排除一半搜索空间是安全的。
        - 最优性：决策树至少需区分 m+1 种分割，下界为 Ω(log m)。

    Args:
        nums1: 第一个有序数组。
        nums2: 第二个有序数组。

    Returns:
        两个数组的中位数。
    """
    # 确保 nums1 是较短的数组
    if len(nums1) > len(nums2):
        nums1, nums2 = nums2, nums1

    m, n = len(nums1), len(nums2)
    total_left = (m + n + 1) // 2

    left, right = 0, m
    while left <= right:
        i = left + (right - left) // 2
        j = total_left - i

        nums1_left_max = float('-inf') if i == 0 else nums1[i - 1]
        nums1_right_min = float('inf') if i == m else nums1[i]
        nums2_left_max = float('-inf') if j == 0 else nums2[j - 1]
        nums2_right_min = float('inf') if j == n else nums2[j]

        if nums1_left_max <= nums2_right_min and nums2_left_max <= nums1_right_min:
            # 找到正确分割
            if (m + n) % 2 == 1:
                return float(max(nums1_left_max, nums2_left_max))
            else:
                return (max(nums1_left_max, nums2_left_max) + min(nums1_right_min, nums2_right_min)) / 2.0
        elif nums1_left_max > nums2_right_min:
            # i 过大，需要减小
            right = i - 1
        else:
            # i 过小，需要增大
            left = i + 1

    # 理论上不会到达这里
    raise ValueError("Input arrays may not be sorted")


if __name__ == "__main__":
    # LeetCode 官方示例
    assert find_median_sorted_arrays([1, 3], [2]) == 2.0, "Example 1 failed"
    assert find_median_sorted_arrays([1, 2], [3, 4]) == 2.5, "Example 2 failed"

    # 边界条件
    assert find_median_sorted_arrays([], [1]) == 1.0, "Single element"
    assert find_median_sorted_arrays([2], []) == 2.0, "Single element other"
    assert find_median_sorted_arrays([1, 2, 3], [4, 5, 6]) == 3.5, "Interleaved"
    assert find_median_sorted_arrays([1, 2], [1, 2, 3]) == 2.0, "Different lengths"
    assert find_median_sorted_arrays([1, 1, 1], [1, 1]) == 1.0, "All same"

    print("All tests passed.")
