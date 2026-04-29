"""LeetCode 153. 寻找旋转排序数组中的最小值 — Python 实现

已知一个长度为 n 的数组，预先按照升序排列，经由 1 到 n 次旋转后，得到输入数组。
数组中的值互不相同。返回数组中的最小元素。

对标: LeetCode 153 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
"""


def find_min(nums: list[int]) -> int:
    """寻找旋转排序数组中的最小值。

    前置条件 (Pre):
        - nums 为某个升序无重复数组经若干次旋转所得。
        - 数组长度 >= 1。

    后置条件 (Post):
        - 返回 nums 中最小元素的值，即 min(nums)。

    循环不变式:
        设当前搜索区间为 [left, right]（闭区间）。
        最小元素始终位于 [left, right] 范围内。

        维护：
        - 初始 left = 0，right = n - 1，不变式显然成立。
        - 取 mid = left + (right - left) // 2：
          * 若 nums[mid] > nums[right]，最小值在右半部分，left = mid + 1。
          * 若 nums[mid] < nums[right]，[mid, right] 整体有序，最小值在左半部分或就是 mid，
            right = mid。
          * 因元素互不相同，不会出现 nums[mid] == nums[right]。
        - 新区间仍包含最小值。

        终止推出：当 left == right 时，区间仅含一个元素，由不变式知其即为最小值。

    复杂度:
        时间复杂度: O(log n) — 每次迭代搜索区间减半。
        空间复杂度: O(1) — 仅使用常数个额外变量。

    证明要点:
        - 关键性质：在旋转排序数组中，nums[mid] 与 nums[right] 的大小关系
          唯一确定了最小值所在的半区。
        - 详细证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
        - 终止性由 left < right 条件及区间长度严格递减保证。

    Args:
        nums: 旋转后的升序无重复整数数组。

    Returns:
        数组中的最小元素值。
    """
    left, right = 0, len(nums) - 1

    while left < right:
        mid = left + (right - left) // 2

        if nums[mid] > nums[right]:
            left = mid + 1
        else:
            # nums[mid] < nums[right]，因元素互不相同
            right = mid

    return nums[left]


if __name__ == "__main__":
    # LeetCode 官方示例
    assert find_min([3, 4, 5, 1, 2]) == 1, "Example 1 failed"
    assert find_min([4, 5, 6, 7, 0, 1, 2]) == 0, "Example 2 failed"
    assert find_min([11, 13, 15, 17]) == 11, "Example 3 failed"

    # 边界条件
    assert find_min([5]) == 5, "Single element"
    assert find_min([2, 1]) == 1, "Two elements rotated"
    assert find_min([1, 2]) == 1, "Two elements not rotated"
    assert find_min([1, 2, 3, 4, 5]) == 1, "Not rotated array"
    assert find_min([2, 3, 4, 5, 1]) == 1, "Target at rotation point end"

    # 大规模测试
    large_nums = list(range(5000, 10_000)) + list(range(0, 5000))
    assert find_min(large_nums) == 0, "Large array minimum"

    print("All tests passed.")
