"""LeetCode 11. 盛最多水的容器 — Python 实现

给定一个长度为 n 的整数数组 height。有 n 条垂线，第 i 条线的两个端点是 (i, 0) 和 (i, height[i])。
找出其中的两条线，使得它们与 x 轴共同构成的容器可以容纳最多的水。
返回容器可以储存的最大水量。

对标: LeetCode 11 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md
"""


def max_area(height: list[int]) -> int:
    """计算能容纳最多水的容器面积。

    前置条件 (Pre):
        - height 为整数数组，长度 n 范围 [2, 10^5]。
        - 每个 height[i] 范围 [0, 10^4]。

    后置条件 (Post):
        - 返回 max_{0 <= i < j < n} min(height[i], height[j]) * (j - i)。

    核心思路:
        双指针法：初始化 left = 0, right = n - 1。
        当前面积由较短的板决定。若向内移动较长的板，面积不可能增大
        （宽度减小，高度不增加）；因此移动较短的板以寻求更高的高度。

    循环不变式:
        设当前指针为 l, r，已遍历的所有以 l' < l 或 r' > r 为边界的
        容器面积均已考察过。剩余未考察的容器边界满足 l <= i < j <= r。

    复杂度:
        时间复杂度: O(n) — 双指针各移动至多 n 次。
        空间复杂度: O(1) — 仅使用常数个额外变量。

    证明要点:
        - 贪心正确性：对于状态 (l, r)，设 height[l] <= height[r]。
          对于任何 k ∈ (l, r)，area(l, k) = min(height[l], height[k]) * (k-l)。
          由于 k-l < r-l 且 height[l] <= height[r]，
          area(l, k) <= height[l] * (k-l) < height[l] * (r-l) = area(l, r)。
          因此以 l 为左边界且右边界在 (l, r) 内的所有容器面积均小于 area(l, r)，
          可以安全地排除 l 而不遗漏最优解。

    Args:
        height: 每条垂线的高度数组。

    Returns:
        最大容器面积。
    """
    left, right = 0, len(height) - 1
    best = 0
    while left < right:
        width = right - left
        if height[left] < height[right]:
            best = max(best, height[left] * width)
            left += 1
        else:
            best = max(best, height[right] * width)
            right -= 1
    return best


if __name__ == "__main__":
    # LeetCode 官方示例
    assert max_area([1, 8, 6, 2, 5, 4, 8, 3, 7]) == 49, "Example 1 failed"
    assert max_area([1, 1]) == 1, "Example 2 failed"

    # 边界条件
    assert max_area([0, 0]) == 0, "All zeros"
    assert max_area([1, 2, 3, 4, 5]) == 6, "Monotonic increasing"
    assert max_area([5, 4, 3, 2, 1]) == 6, "Monotonic decreasing"
    assert max_area([2, 3, 4, 5, 18, 17, 6]) == 17, "Tall in middle"

    # 大规模测试
    large_height = list(range(5_000)) + list(range(5_000, 0, -1))
    result = max_area(large_height)
    assert result > 0, "Large array should have positive area"

    print("All tests passed.")
