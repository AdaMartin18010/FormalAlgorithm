"""
LeetCode 223. Rectangle Area
链接: https://leetcode.com/problems/rectangle-area/
难度: Medium

题目描述:
给你二维平面上两个由直线构成且边与坐标轴平行的矩形，请你计算并返回两个矩形覆盖的总面积。
每个矩形由其左下顶点和右上顶点坐标表示。

形式化规约:
  输入: 矩形A(ax1, ay1, ax2, ay2), 矩形B(bx1, by1, bx2, by2)
  输出: 两个矩形并集的面积 |A ∪ B|

最优解思路:
  容斥原理：总面积 = area(A) + area(B) - area(A ∩ B)。
  重叠区域（若存在）也是轴对齐矩形：
    left   = max(ax1, bx1)
    right  = min(ax2, bx2)
    bottom = max(ay1, by1)
    top    = min(ay2, by2)
  当 left < right 且 bottom < top 时存在重叠，面积为 (right-left)*(top-bottom)。

复杂度:
  时间: O(1)
  空间: O(1)

正确性要点:
  1. 并集面积 = 各自面积之和 - 交集面积（容斥原理）
  2. 交集存在当且仅当 x 轴和 y 轴投影均相交
  3. 使用整数运算避免浮点误差，注意大数时用长整型防止溢出
"""


class Solution:
    def computeArea(
        self,
        ax1: int,
        ay1: int,
        ax2: int,
        ay2: int,
        bx1: int,
        by1: int,
        bx2: int,
        by2: int,
    ) -> int:
        """
        计算两个轴对齐矩形覆盖的总面积。
        时间复杂度 O(1)，空间复杂度 O(1)。
        """
        area_a = (ax2 - ax1) * (ay2 - ay1)
        area_b = (bx2 - bx1) * (by2 - by1)

        left = max(ax1, bx1)
        right = min(ax2, bx2)
        bottom = max(ay1, by1)
        top = min(ay2, by2)

        overlap = 0
        if left < right and bottom < top:
            overlap = (right - left) * (top - bottom)

        return area_a + area_b - overlap


def test_compute_area():
    sol = Solution()

    # 示例 1
    assert sol.computeArea(-3, 0, 3, 4, 0, -1, 9, 2) == 45, "Test 1 failed"

    # 示例 2：无重叠
    assert sol.computeArea(-2, -2, 2, 2, -4, -4, -3, -3) == 17, "Test 2 failed"

    # 部分重叠
    assert sol.computeArea(0, 0, 2, 2, 1, 1, 3, 3) == 7, "Test partial overlap failed"

    # 一个包含另一个
    assert sol.computeArea(0, 0, 4, 4, 1, 1, 2, 2) == 16, "Test contain failed"

    # 边相接（无重叠）
    assert sol.computeArea(0, 0, 2, 2, 2, 0, 4, 2) == 8, "Test edge touch failed"

    # 角相接（无重叠）
    assert sol.computeArea(0, 0, 1, 1, 1, 1, 2, 2) == 2, "Test corner touch failed"

    # 大数值测试
    assert (
        sol.computeArea(-10_000, -10_000, 10_000, 10_000, -10_000, -10_000, 10_000, 10_000)
        == 400_000_000
    ), "Test large failed"

    print("All tests passed for LC 223 - Rectangle Area")


if __name__ == "__main__":
    test_compute_area()
