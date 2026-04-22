"""LeetCode 26. 删除有序数组中的重复项 — Python 实现

给你一个非严格递增排列的数组 nums，原地删除重复出现的元素，使每个元素只出现一次。
返回删除后数组的新长度。

对标: LeetCode 26 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
"""

from typing import List


def remove_duplicates(nums: List[int]) -> int:
    """原地删除有序数组中的重复元素，返回新长度。

    前置条件 (Pre):
        - nums 为按非降序排列的整数数组，长度 ∈ [0, 3 * 10^4]。
        - nums[i] ∈ [-10^4, 10^4]。

    后置条件 (Post):
        - 返回 k，表示去重后数组的长度。
        - nums 的前 k 个元素为去重后的结果，按原顺序排列。
        - nums[k:] 的内容不做要求。
        - 前 k 个元素中每个值恰好出现一次。

    算法框架:
        快慢指针：slow 指向去重后数组的下一个写入位置，fast 扫描原数组。
        当 nums[fast] != nums[slow-1] 时，将 nums[fast] 复制到 nums[slow]。

    循环不变式:
        在每次迭代开始时：
        - nums[0..slow-1] 为已处理的去重结果，无重复元素。
        - nums[0..slow-1] 恰好是 nums[0..fast-1] 中所有不同元素按原顺序的排列。

        维护：
        - 初始 slow = 1, fast = 1（或 slow = 0, fast = 0 的空数组处理）。
        - 若 nums[fast] == nums[slow-1]：fast 所指的元素重复，仅 fast += 1。
        - 若 nums[fast] != nums[slow-1]：发现新元素，nums[slow] = nums[fast]，然后两者均 += 1。
        - 无论哪种情况，nums[0..slow-1] 的去重性质保持不变。

        终止推出：
        fast 到达 n 时，nums[0..slow-1] 即为完整去重结果，返回 slow。

    复杂度:
        时间复杂度: O(n) — fast 指针遍历数组一次。
        空间复杂度: O(1) — 仅使用 slow, fast 两个指针，原地修改数组。

    证明要点:
        - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
        - 关键：排序保证相同元素连续出现，故只需比较相邻元素即可判断是否重复。

    Args:
        nums: 按非降序排列的整数数组（原地修改）。

    Returns:
        去重后数组的新长度 k。
    """
    if not nums:
        return 0

    slow = 1
    for fast in range(1, len(nums)):
        if nums[fast] != nums[slow - 1]:
            nums[slow] = nums[fast]
            slow += 1

    return slow


if __name__ == "__main__":
    # 示例 1
    nums1 = [1, 1, 2]
    k1 = remove_duplicates(nums1)
    assert k1 == 2, f"Example 1 length failed: {k1}"
    assert nums1[:k1] == [1, 2], f"Example 1 content failed: {nums1[:k1]}"

    # 示例 2
    nums2 = [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
    k2 = remove_duplicates(nums2)
    assert k2 == 5, f"Example 2 length failed: {k2}"
    assert nums2[:k2] == [0, 1, 2, 3, 4], f"Example 2 content failed: {nums2[:k2]}"

    # 边界：空数组
    nums_empty: List[int] = []
    assert remove_duplicates(nums_empty) == 0, "Empty array"

    # 边界：单元素
    nums_single = [5]
    k_single = remove_duplicates(nums_single)
    assert k_single == 1
    assert nums_single[:k_single] == [5]

    # 边界：全不同
    nums_distinct = [1, 2, 3, 4, 5]
    k_distinct = remove_duplicates(nums_distinct)
    assert k_distinct == 5
    assert nums_distinct[:k_distinct] == [1, 2, 3, 4, 5]

    # 边界：全相同
    nums_same = [2, 2, 2, 2, 2]
    k_same = remove_duplicates(nums_same)
    assert k_same == 1
    assert nums_same[:k_same] == [2]

    # 边界：负数
    nums_neg = [-3, -3, -2, -1, -1, 0, 0]
    k_neg = remove_duplicates(nums_neg)
    assert k_neg == 4
    assert nums_neg[:k_neg] == [-3, -2, -1, 0]

    print("All tests passed.")
