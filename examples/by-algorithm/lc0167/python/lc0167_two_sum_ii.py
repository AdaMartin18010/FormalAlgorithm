"""LeetCode 167. 两数之和 II — 输入数组已排序 — Python 实现

给定一个已按非降序排列的数组 numbers，找出两个数使它们的和等于目标数 target。
返回它们的索引（从 1 开始计数）。

对标: LeetCode 167 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
"""

from typing import List


def two_sum(numbers: List[int], target: int) -> List[int]:
    """在已排序数组中找到和为目标值的两个数的索引（1-based）。

    前置条件 (Pre):
        - numbers 为按非降序排列的整数数组，长度 ∈ [2, 3 * 10^4]。
        - numbers[i] ∈ [-10^3, 10^3]。
        - 题目保证恰好存在一个有效答案，且同一个元素不能使用两遍。

    后置条件 (Post):
        - 返回 [i, j]，满足 numbers[i-1] + numbers[j-1] == target，且 i < j。

    算法框架:
        对撞指针：l 从 0 开始，r 从末尾开始。
        根据两数之和与 target 的比较结果移动指针。

    循环不变式:
        设当前指针为 l, r。
        不变式：若解存在，则解的两个索引必在 [l, r] 范围内。

        维护：
        - 初始 l = 0, r = n-1，显然成立（解在全局范围内）。
        - 设 sum = numbers[l] + numbers[r]：
          * sum == target：找到解，返回。
          * sum < target：numbers[l] 太小，任何 k < r 的配对 (l, k) 都有
            numbers[l] + numbers[k] ≤ numbers[l] + numbers[r] < target，
            故 l 不可能再与任何左侧指针构成解，l += 1。
          * sum > target：numbers[r] 太大，任何 k > l 的配对 (k, r) 都有
            numbers[k] + numbers[r] ≥ numbers[l] + numbers[r] > target，
            故 r 不可能再与任何右侧指针构成解，r -= 1。
        - 每次移动都排除了当前指针不可能参与解的情况。

    复杂度:
        时间复杂度: O(n) — 每轮迭代 l 或 r 向中间移动一步，最多 n-1 轮。
        空间复杂度: O(1) — 仅使用两个指针变量。

    证明要点:
        - 不遗漏解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
        - 核心：排序保证排除操作的单调性，移动矮/高边板的逻辑与 LC 11 类似。

    Args:
        numbers: 已按非降序排列的整数数组。
        target: 目标和。

    Returns:
        两个数的 1-based 索引 [i, j]，满足 i < j。
    """
    left, right = 0, len(numbers) - 1

    while left < right:
        current_sum = numbers[left] + numbers[right]
        if current_sum == target:
            return [left + 1, right + 1]
        elif current_sum < target:
            left += 1
        else:
            right -= 1

    # 根据前置条件，必存在解，此处不应到达
    return [-1, -1]


if __name__ == "__main__":
    # 示例 1
    assert two_sum([2, 7, 11, 15], 9) == [1, 2], "Example 1 failed"

    # 示例 2
    assert two_sum([2, 3, 4], 6) == [1, 3], "Example 2 failed"

    # 示例 3
    assert two_sum([-1, 0], -1) == [1, 2], "Example 3 failed"

    # 边界：两个元素
    assert two_sum([1, 2], 3) == [1, 2], "Two elements"

    # 边界：负数
    assert two_sum([-5, -3, -1, 0, 2], -8) == [1, 2], "Negative numbers"

    # 边界：包含零
    assert two_sum([0, 0, 3, 4], 0) == [1, 2], "Zero sum"

    # 边界：大数组
    large = list(range(1, 10001))
    assert two_sum(large, 19999) == [9999, 10000], "Large array"

    print("All tests passed.")
