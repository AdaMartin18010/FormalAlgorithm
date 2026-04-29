"""LeetCode 912. 排序数组 — Python 实现

给你一个整数数组 nums，请你将该数组升序排列。

对标: LeetCode 912 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
"""

from typing import List


def sort_array(nums: List[int]) -> List[int]:
    """使用归并排序将数组升序排列。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [1, 5·10^4]。

    后置条件 (Post):
        - 返回 nums 的一个非降序排列（元素多重集相同）。

    核心思路:
        分治归并排序：
        1. 分解：将数组从中间分为两半。
        2. 解决：递归对左右两半分别排序。
        3. 合并：将两个已排序的子数组合并为一个有序数组。

    复杂度:
        时间复杂度: O(n log n) — 递归树深度 log n，每层合并 O(n)。
        空间复杂度: O(n) — 合并过程需要辅助数组。

    证明要点:
        - 引理：合并两个有序数组的算法产生一个有序数组，且包含两个数组的所有元素。
        - 对数组长度进行强归纳，证明归并排序返回非降序排列。

    Args:
        nums: 输入整数数组。

    Returns:
        升序排列后的数组。
    """
    if len(nums) <= 1:
        return nums[:]

    mid = len(nums) // 2
    left = sort_array(nums[:mid])
    right = sort_array(nums[mid:])

    return _merge(left, right)


def _merge(left: List[int], right: List[int]) -> List[int]:
    """合并两个有序数组。"""
    result = []
    i = j = 0

    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1

    result.extend(left[i:])
    result.extend(right[j:])
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert sort_array([5, 2, 3, 1]) == [1, 2, 3, 5], "Example 1 failed"
    assert sort_array([5, 1, 1, 2, 0, 0]) == [0, 0, 1, 1, 2, 5], "Example 2 failed"

    # 边界条件
    assert sort_array([1]) == [1], "Single element"
    assert sort_array([2, 1]) == [1, 2], "Two elements"
    assert sort_array([3, 3, 3]) == [3, 3, 3], "All same"
    assert sort_array([-1, -5, 0, 2]) == [-5, -1, 0, 2], "Negative numbers"

    print("All tests passed.")
