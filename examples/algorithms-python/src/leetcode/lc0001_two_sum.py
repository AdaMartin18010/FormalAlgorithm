"""LeetCode 1. 两数之和 — Python 实现

给定一个整数数组 nums 和一个整数目标值 target，
请你在该数组中找出和为目标值 target 的那两个整数，并返回它们的数组下标。

对标: LeetCode 1 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md
"""


def two_sum(nums: list[int], target: int) -> list[int]:
    """在数组中找出和为 target 的两个元素的索引。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [2, 10^4]。
        - 数组中存在恰好一个满足条件的解，同一元素不能重复使用。

    后置条件 (Post):
        - 返回列表 [i, j] 满足 i != j 且 nums[i] + nums[j] == target。

    核心思路:
        使用哈希表（字典）记录已遍历元素值到索引的映射。
        对于当前元素 nums[j]，若 target - nums[j] 已在哈希表中，
        则找到配对；否则将 nums[j] 加入哈希表。

    复杂度:
        时间复杂度: O(n) — 单次遍历数组。
        空间复杂度: O(n) — 哈希表最多存储 n 个元素。

    证明要点:
        - 正确性：若解为 (i, j) 且 i < j，当遍历到 j 时，
          target - nums[j] = nums[i] 已在哈希表中，故必能找到。
        - 唯一性：题目保证恰好一个解。

    Args:
        nums: 整数数组。
        target: 目标和。

    Returns:
        两个索引组成的列表 [i, j]。
    """
    seen: dict[int, int] = {}
    for j, num in enumerate(nums):
        complement = target - num
        if complement in seen:
            return [seen[complement], j]
        seen[num] = j
    return []


if __name__ == "__main__":
    # LeetCode 官方示例
    assert two_sum([2, 7, 11, 15], 9) == [0, 1], "Example 1 failed"
    assert two_sum([3, 2, 4], 6) == [1, 2], "Example 2 failed"
    assert two_sum([3, 3], 6) == [0, 1], "Example 3 failed"

    # 边界条件
    assert two_sum([1, 2, 3, 4, 5], 9) == [3, 4], "Boundary right side"
    assert two_sum([-1, -2, -3, -4, -5], -8) == [2, 4], "Negative numbers"
    assert two_sum([0, 4, 3, 0], 0) == [0, 3], "Zeros"

    # 大规模测试
    large_nums = list(range(10_000))
    result = two_sum(large_nums, 19_997)
    assert result == [9998, 9999], f"Large array failed: {result}"

    print("All tests passed.")
