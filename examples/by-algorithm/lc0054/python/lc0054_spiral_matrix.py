"""
LeetCode 54 - Spiral Matrix
https://leetcode.com/problems/spiral-matrix/

题目：给定一个 m x n 矩阵，按顺时针螺旋顺序返回所有元素。

思路：维护四个边界 top, bottom, left, right，按顺序遍历顶行、右列、底行、左列，
      然后收缩边界，直到边界交错。
时间复杂度：O(m * n)
空间复杂度：O(1)，不计输出数组
"""

from typing import List


class Solution:
    def spiralOrder(self, matrix: List[List[int]]) -> List[int]:
        if not matrix or not matrix[0]:
            return []

        result = []
        top, bottom = 0, len(matrix) - 1
        left, right = 0, len(matrix[0]) - 1

        while top <= bottom and left <= right:
            # 顶行：从左到右
            for col in range(left, right + 1):
                result.append(matrix[top][col])
            top += 1

            # 右列：从上到下
            for row in range(top, bottom + 1):
                result.append(matrix[row][right])
            right -= 1

            # 底行：从右到左（需检查是否还有有效行）
            if top <= bottom:
                for col in range(right, left - 1, -1):
                    result.append(matrix[bottom][col])
                bottom -= 1

            # 左列：从下到上（需检查是否还有有效列）
            if left <= right:
                for row in range(bottom, top - 1, -1):
                    result.append(matrix[row][left])
                left += 1

        return result


def test_spiral_order():
    sol = Solution()

    # 测试用例1：3x3 矩阵
    m1 = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
    ]
    assert sol.spiralOrder(m1) == [1, 2, 3, 6, 9, 8, 7, 4, 5], "Test 1 failed"

    # 测试用例2：3x4 矩阵
    m2 = [
        [1, 2, 3, 4],
        [5, 6, 7, 8],
        [9, 10, 11, 12],
    ]
    assert sol.spiralOrder(m2) == [1, 2, 3, 4, 8, 12, 11, 10, 9, 5, 6, 7], "Test 2 failed"

    # 测试用例3：1x1 矩阵
    m3 = [[7]]
    assert sol.spiralOrder(m3) == [7], "Test 3 failed"

    # 测试用例4：1x5 矩阵（单行）
    m4 = [[1, 2, 3, 4, 5]]
    assert sol.spiralOrder(m4) == [1, 2, 3, 4, 5], "Test 4 failed"

    # 测试用例5：5x1 矩阵（单列）
    m5 = [[1], [2], [3], [4], [5]]
    assert sol.spiralOrder(m5) == [1, 2, 3, 4, 5], "Test 5 failed"

    # 测试用例6：空矩阵
    assert sol.spiralOrder([]) == [], "Test 6 failed"
    assert sol.spiralOrder([[]]) == [], "Test 7 failed"

    print("All tests passed for LC 54 - Spiral Matrix")


if __name__ == "__main__":
    test_spiral_order()
