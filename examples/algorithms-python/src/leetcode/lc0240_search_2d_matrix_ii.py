"""
LeetCode 240 - Search a 2D Matrix II
https://leetcode.com/problems/search-a-2d-matrix-ii/

题目：编写一个高效的算法来搜索 m x n 矩阵中的一个目标值 target。
      该矩阵具有以下特性：
      - 每行从左到右升序排列
      - 每列从上到下升序排列

思路：从右上角开始搜索。
      - 若当前值 == target，返回 True
      - 若当前值 > target，排除当前列（向左移动）
      - 若当前值 < target，排除当前行（向下移动）
时间复杂度：O(m + n)
空间复杂度：O(1)
"""

from typing import List


class Solution:
    def searchMatrix(self, matrix: List[List[int]], target: int) -> bool:
        if not matrix or not matrix[0]:
            return False

        m, n = len(matrix), len(matrix[0])
        row, col = 0, n - 1  # 从右上角开始

        while row < m and col >= 0:
            if matrix[row][col] == target:
                return True
            elif matrix[row][col] > target:
                col -= 1  # 排除当前列
            else:
                row += 1  # 排除当前行

        return False


def test_search_matrix():
    sol = Solution()

    # 测试用例1
    matrix1 = [
        [1, 4, 7, 11, 15],
        [2, 5, 8, 12, 19],
        [3, 6, 9, 16, 22],
        [10, 13, 14, 17, 24],
        [18, 21, 23, 26, 30],
    ]
    assert sol.searchMatrix(matrix1, 5) == True, "Test 1 failed"
    assert sol.searchMatrix(matrix1, 20) == False, "Test 2 failed"
    assert sol.searchMatrix(matrix1, 1) == True, "Test 3 failed"
    assert sol.searchMatrix(matrix1, 30) == True, "Test 4 failed"
    assert sol.searchMatrix(matrix1, 18) == True, "Test 5 failed"

    # 测试用例2：空矩阵
    assert sol.searchMatrix([], 1) == False, "Test 6 failed"
    assert sol.searchMatrix([[]], 1) == False, "Test 7 failed"

    # 测试用例3：1x1 矩阵
    assert sol.searchMatrix([[1]], 1) == True, "Test 8 failed"
    assert sol.searchMatrix([[1]], 2) == False, "Test 9 failed"

    # 测试用例4：比所有元素都小/大
    assert sol.searchMatrix(matrix1, 0) == False, "Test 10 failed"
    assert sol.searchMatrix(matrix1, 100) == False, "Test 11 failed"

    print("All tests passed for LC 240 - Search a 2D Matrix II")


if __name__ == "__main__":
    test_search_matrix()
