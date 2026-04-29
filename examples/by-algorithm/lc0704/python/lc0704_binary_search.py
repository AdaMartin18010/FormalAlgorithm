"""LeetCode 704. 二分查找 — Python 实现

给定一个 n 个元素有序的（升序）整型数组 nums 和一个目标值 target，
写一个函数搜索 nums 中的 target，如果目标值存在返回下标，否则返回 -1。

对标: LeetCode 704 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
"""


def search(nums: list[int], target: int) -> int:
    """在有序数组中查找目标值的索引。

    前置条件 (Pre):
        - nums 为升序排列的整数数组。
        - 元素取值范围为 [-10^4, 10^4]，数组长度范围为 [0, 10^4]。

    后置条件 (Post):
        - 若 target 在 nums 中，返回其索引 i 满足 nums[i] == target。
        - 若 target 不在 nums 中，返回 -1。

    循环不变式:
        设当前搜索区间为 [left, right]（闭区间）。
        若 target 存在于 nums，则其索引必然位于 [left, right] 之内。

        维护：
        - 初始 left = 0，right = n - 1，不变式显然成立。
        - 取 mid = left + (right - left) // 2：
          * 若 nums[mid] == target，已找到，返回 mid。
          * 若 nums[mid] < target，目标若在数组中必在右半区，left = mid + 1。
          * 若 nums[mid] > target，目标若在数组中必在左半区，right = mid - 1。
        - 新区间仍包含可能的目标索引。

        终止推出：当 left > right 时区间为空，由不变式知 target 不在数组中，返回 -1。

    复杂度:
        时间复杂度: O(log n) — 每次迭代搜索区间减半。
        空间复杂度: O(1) — 仅使用常数个额外变量。

    证明要点:
        - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
        - 终止性由区间长度严格递减保证。

    Args:
        nums: 升序排列的整数数组。
        target: 待查找的目标值。

    Returns:
        target 的索引，若不存在则返回 -1。
    """
    left, right = 0, len(nums) - 1

    while left <= right:
        mid = left + (right - left) // 2
        mid_val = nums[mid]

        if mid_val == target:
            return mid

        if mid_val < target:
            left = mid + 1
        else:
            right = mid - 1

    return -1


if __name__ == "__main__":
    # LeetCode 官方示例
    assert search([-1, 0, 3, 5, 9, 12], 9) == 4, "Example 1 failed"
    assert search([-1, 0, 3, 5, 9, 12], 2) == -1, "Example 2 failed"

    # 边界条件
    assert search([], 1) == -1, "Empty array should return -1"
    assert search([5], 5) == 0, "Single element found"
    assert search([5], 1) == -1, "Single element not found"
    assert search([2, 2, 2, 2], 2) == 1, "All same elements found"
    assert search([2, 2, 2, 2], 3) == -1, "All same elements not found"
    assert search([1, 2, 3, 4, 5], 1) == 0, "Target at left boundary"
    assert search([1, 2, 3, 4, 5], 5) == 4, "Target at right boundary"

    # 大规模测试
    large_nums = list(range(10_000))
    assert search(large_nums, 5_000) == 5_000, "Large array target found"
    assert search(large_nums, 10_001) == -1, "Large array target not found"

    print("All tests passed.")
