"""LeetCode 209. 长度最小的子数组 — Python 实现

给定一个含有 n 个正整数的数组 nums 和一个正整数 target，
找出该数组中满足其和 ≥ target 的长度最小的连续子数组，并返回其长度。
如果不存在符合条件的子数组，返回 0。

对标: LeetCode 209 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
"""

from typing import List


def min_sub_array_len(target: int, nums: List[int]) -> int:
    """找出和大于等于 target 的最短连续子数组长度。

    前置条件 (Pre):
        - nums 为正整数数组，长度 ∈ [1, 10^5]。
        - nums[i] ∈ [1, 10^4]，target ∈ [1, 10^9]。

    后置条件 (Post):
        - 返回 min_{0 ≤ l ≤ r < n, sum(nums[l..r]) ≥ target} (r - l + 1)。
        - 若不存在这样的子数组，返回 0。

    算法框架:
        滑动窗口：维护窗口 [left, right] 的和 window_sum。
        当 window_sum ≥ target 时，尝试收缩 left 以寻找更短子数组。

    窗口不变式 WindowInvariant(left, right):
        window_sum = sum(nums[left..right])。
        在扩展阶段，窗口和可能 < target（继续扩展）或 ≥ target（尝试收缩）。

        关键引理（收缩的正确性）：
        若当前窗口 [left, right] 满足 window_sum ≥ target，
        则对于任何 left' > left，窗口 [left', right] 的长度更小。
        若 [left', right] 仍满足和 ≥ target，则找到了更优（更短）的候选解。
        因此可安全地将 left 右移以探索更短窗口。

        维护：
        - 初始 left = 0, window_sum = 0。
        - 扩展 right：window_sum += nums[right]。
        - 当 window_sum ≥ target 时：
          * 更新最小长度。
          * window_sum -= nums[left]，left += 1（尝试收缩）。
        - 重复收缩直到 window_sum < target，继续扩展 right。

    复杂度:
        时间复杂度: O(n) — 摊还分析：right 遍历 n 次，left 最多移动 n 次，总计 O(n)。
        空间复杂度: O(1) — 仅使用 left, right, window_sum, min_len。

    证明要点:
        - 窗口收缩正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
        - 摊还分析：每个元素最多被加入窗口一次、移出窗口一次。

    Args:
        target: 目标和阈值。
        nums: 正整数数组。

    Returns:
        满足条件的最短连续子数组长度，若不存在则返回 0。
    """
    n = len(nums)
    min_len = n + 1
    left = 0
    window_sum = 0

    for right in range(n):
        window_sum += nums[right]
        while window_sum >= target:
            min_len = min(min_len, right - left + 1)
            window_sum -= nums[left]
            left += 1

    return 0 if min_len == n + 1 else min_len


if __name__ == "__main__":
    # 示例 1
    assert min_sub_array_len(7, [2, 3, 1, 2, 4, 3]) == 2, "Example 1 failed"

    # 示例 2
    assert min_sub_array_len(4, [1, 4, 4]) == 1, "Example 2 failed"

    # 示例 3
    assert min_sub_array_len(11, [1, 1, 1, 1, 1, 1, 1, 1]) == 0, "Example 3 failed"

    # 边界：单元素满足
    assert min_sub_array_len(5, [5]) == 1, "Single element exact"

    # 边界：单元素不满足
    assert min_sub_array_len(5, [3]) == 0, "Single element insufficient"

    # 边界：整个数组和刚好满足
    assert min_sub_array_len(10, [1, 2, 3, 4]) == 4, "Whole array exact"

    # 边界：最短子数组在末尾
    assert min_sub_array_len(15, [1, 2, 3, 10, 5]) == 1, "Single large at end"

    # 大规模测试
    large = [1] * 100000
    assert min_sub_array_len(100000, large) == 100000, "Large array"
    assert min_sub_array_len(50000, large) == 50000, "Large array half"

    print("All tests passed.")
