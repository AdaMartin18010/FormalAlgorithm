"""
LeetCode 48 - Rotate Image
https://leetcode.com/problems/rotate-image/

题目：给定一个 n × n 的二维矩阵 matrix ，将矩阵顺时针旋转 90 度（原地）。

思路：先转置矩阵，再水平翻转每一行。
时间复杂度：O(n^2)
空间复杂度：O(1)
"""

from typing import List


class Solution:
    def rotate(self, matrix: List[List[int]]) -> None:
        """
        Do not return anything, modify matrix in-place instead.
        """
        n = len(matrix)
        if n == 0:
            return

        # 步骤1：转置矩阵（对角线翻转）
        # matrix[i][j] <-> matrix[j][i]
        for i in range(n):
            for j in range(i + 1, n):
                matrix[i][j], matrix[j][i] = matrix[j][i], matrix[i][j]

        # 步骤2：水平翻转每一行
        for i in range(n):
            matrix[i].reverse()


def test_rotate():
    sol = Solution()

    # 测试用例1：3x3 矩阵
    m1 = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
    ]
    sol.rotate(m1)
    assert m1 == [
        [7, 4, 1],
        [8, 5, 2],
        [9, 6, 3],
    ], f"Test 1 failed: {m1}"

    # 测试用例2：4x4 矩阵
    m2 = [
        [5, 1, 9, 11],
        [2, 4, 8, 10],
        [13, 3, 6, 7],
        [15, 14, 12, 16],
    ]
    sol.rotate(m2)
    assert m2 == [
        [15, 13, 2, 5],
        [14, 3, 4, 1],
        [12, 6, 8, 9],
        [16, 7, 10, 11],
    ], f"Test 2 failed: {m2}"

    # 测试用例3：1x1 矩阵（边界条件）
    m3 = [[1]]
    sol.rotate(m3)
    assert m3 == [[1]], f"Test 3 failed: {m3}"

    # 测试用例4：2x2 矩阵
    m4 = [
        [1, 2],
        [3, 4],
    ]
    sol.rotate(m4)
    assert m4 == [
        [3, 1],
        [4, 2],
    ], f"Test 4 failed: {m4}"

    print("All tests passed for LC 48 - Rotate Image")


if __name__ == "__main__":
    test_rotate()
