"""LeetCode 33. 搜索旋转排序数组 — Python 实现

整数数组 nums 按升序排列，数组中的值互不相同。
在传递给函数之前，nums 在预先未知的某个下标 k 处进行了旋转。
给定旋转后的数组 nums 和一个整数 target，如果 nums 中存在这个目标值 target，
则返回它的下标，否则返回 -1。

对标: LeetCode 33 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
"""


def search(nums: list[int], target: int) -> int:
    """在旋转排序数组中搜索目标值的索引。

    前置条件 (Pre):
        - nums 为某个升序无重复数组经一次旋转所得。
        - 数组长度范围为 [0, 5000]。

    后置条件 (Post):
        - 若 target 在 nums 中，返回其索引 i 满足 nums[i] == target。
        - 若 target 不在 nums 中，返回 -1。

    循环不变式:
        设当前搜索区间为 [left, right]（闭区间）。
        若 target 存在于 nums，则其索引必然位于 [left, right] 之内。

        维护：
        - 旋转数组的性质：至少有一半是有序的。
        - 取 mid = left + (right - left) // 2：
          * 若 nums[left] <= nums[mid]，左半部分有序：
            - 若 target 落在 [nums[left], nums[mid])，right = mid - 1。
            - 否则 left = mid + 1。
          * 若 nums[left] > nums[mid]，右半部分有序：
            - 若 target 落在 (nums[mid], nums[right]]，left = mid + 1。
            - 否则 right = mid - 1。
        - 新区间仍包含可能的目标索引。

        终止推出：当 left > right 时区间为空，由不变式知 target 不在数组中，返回 -1。

    复杂度:
        时间复杂度: O(log n) — 每次迭代搜索区间减半。
        空间复杂度: O(1) — 仅使用常数个额外变量。

    证明要点:
        - 正确性依赖于「旋转排序数组中至少有一半是有序的」这一性质。
        - 详细证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
        - 终止性由区间长度严格递减保证。

    Args:
        nums: 旋转后的升序无重复整数数组。
        target: 待查找的目标值。

    Returns:
        target 的索引，若不存在则返回 -1。
    """
    if not nums:
        return -1

    left, right = 0, len(nums) - 1

    while left <= right:
        mid = left + (right - left) // 2
        mid_val = nums[mid]

        if mid_val == target:
            return mid

        left_val = nums[left]

        if left_val <= mid_val:
            # 左半部分有序
            if left_val <= target < mid_val:
                right = mid - 1
            else:
                left = mid + 1
        else:
            # 右半部分有序
            right_val = nums[right]
            if mid_val < target <= right_val:
                left = mid + 1
            else:
                right = mid - 1

    return -1


if __name__ == "__main__":
    # LeetCode 官方示例
    assert search([4, 5, 6, 7, 0, 1, 2], 0) == 4, "Example 1 failed"
    assert search([4, 5, 6, 7, 0, 1, 2], 3) == -1, "Example 2 failed"
    assert search([1], 0) == -1, "Example 3 failed"

    # 边界条件
    assert search([], 1) == -1, "Empty array should return -1"
    assert search([5], 5) == 0, "Single element found"
    assert search([5], 1) == -1, "Single element not found"
    assert search([1, 2, 3, 4, 5], 3) == 2, "Not rotated array"
    assert search([1, 2, 3, 4, 5], 6) == -1, "Not rotated array target not found"
    assert search([3, 4, 5, 1, 2], 1) == 3, "Target at rotation point"

    # 大规模测试
    large_nums = list(range(5000, 10_000)) + list(range(0, 5000))
    assert search(large_nums, 7_500) == 2_500, "Large array target found"
    assert search(large_nums, 10_001) == -1, "Large array target not found"

    print("All tests passed.")
