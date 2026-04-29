"""
LeetCode 48. Rotate Image
链接: https://leetcode.com/problems/rotate-image/
难度: Medium

题目描述:
给定一个 n × n 的二维矩阵 matrix 表示一个图像。请你将图像顺时针旋转 90 度。
你必须在原地旋转图像，这意味着你需要直接修改输入的二维矩阵。请不要使用另一个矩阵来旋转图像。

形式化规约:
  输入: matrix ∈ Z^(n×n)
  输出: 原地修改 matrix，使得新 matrix[j][n-1-i] = 原 matrix[i][j]

最优解思路:
  两步法：先沿主对角线转置（行列互换），再对每行进行水平翻转（左右反转）。
  复合效果等价于顺时针旋转 90 度。

复杂度:
  时间: O(n^2)
  空间: O(1)

正确性要点:
  1. 转置操作将 (i, j) 映射到 (j, i)
  2. 水平翻转将 (j, i) 映射到 (j, n-1-i)
  3. 复合映射正好是顺时针旋转 90 度的坐标变换
"""

from typing import List


class Solution:
    def rotate(self, matrix: List[List[int]]) -> None:
        """
        原地顺时针旋转 n × n 矩阵 90 度。
        时间复杂度 O(n^2)，空间复杂度 O(1)。
        """
        n = len(matrix)
        if n <= 1:
            return

        # 步骤1：转置（沿主对角线交换）
        for i in range(n):
            for j in range(i + 1, n):
                matrix[i][j], matrix[j][i] = matrix[j][i], matrix[i][j]

        # 步骤2：水平翻转（每行左右反转）
        for i in range(n):
            left, right = 0, n - 1
            while left < right:
                matrix[i][left], matrix[i][right] = matrix[i][right], matrix[i][left]
                left += 1
                right -= 1


def test_rotate():
    sol = Solution()

    # 示例 1
    matrix1 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    sol.rotate(matrix1)
    assert matrix1 == [[7, 4, 1], [8, 5, 2], [9, 6, 3]], f"Test 1 failed: {matrix1}"

    # 示例 2
    matrix2 = [
        [5, 1, 9, 11],
        [2, 4, 8, 10],
        [13, 3, 6, 7],
        [15, 14, 12, 16],
    ]
    sol.rotate(matrix2)
    expected2 = [
        [15, 13, 2, 5],
        [14, 3, 4, 1],
        [12, 6, 8, 9],
        [16, 7, 10, 11],
    ]
    assert matrix2 == expected2, f"Test 2 failed: {matrix2}"

    # 边界：单元素
    matrix3 = [[42]]
    sol.rotate(matrix3)
    assert matrix3 == [[42]], f"Test single failed: {matrix3}"

    # 边界：2x2
    matrix4 = [[1, 2], [3, 4]]
    sol.rotate(matrix4)
    assert matrix4 == [[3, 1], [4, 2]], f"Test 2x2 failed: {matrix4}"

    print("All tests passed for LC 48 - Rotate Image")


if __name__ == "__main__":
    test_rotate()
