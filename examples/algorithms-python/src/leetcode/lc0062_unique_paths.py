"""
LeetCode 62. Unique Paths
链接: https://leetcode.com/problems/unique-paths/
难度: Medium

题目描述:
一个机器人位于一个 m × n 网格的左上角。机器人每次只能向下或者向右移动一步。
机器人试图达到网格的右下角。问总共有多少条不同的路径？

形式化规约:
  输入: m, n ∈ Z+，网格行数和列数
  输出: 从 (0,0) 到 (m-1,n-1) 的不同路径总数

最优解思路:
  组合数学：从起点到终点共需走 (m-1)+(n-1) = m+n-2 步，其中恰好有 m-1 步向下。
  路径总数等于从 m+n-2 步中选择 m-1 步向下的组合数 C(m+n-2, m-1)。
  使用递推方式计算，避免阶乘溢出：
    C(a, b) = a*(a-1)*...*(a-b+1) / b! ，其中 b = min(m-1, n-1)

复杂度:
  时间: O(min(m, n))
  空间: O(1)

正确性要点:
  1. 每条路径对应一个由 m-1 个 D 和 n-1 个 R 组成的唯一序列
  2. 序列总数等于二项式系数 C(m+n-2, m-1)
  3. 递推计算时分母整除分子，中间结果始终为整数
"""


class Solution:
    def uniquePaths(self, m: int, n: int) -> int:
        """
        计算从网格左上角到右下角的不同路径总数。
        时间复杂度 O(min(m, n))，空间复杂度 O(1)。
        """
        total = m + n - 2
        k = min(m - 1, n - 1)
        result = 1
        for i in range(k):
            result = result * (total - i) // (i + 1)
        return result


def test_unique_paths():
    sol = Solution()

    # 示例 1
    assert sol.uniquePaths(3, 7) == 28, "Test 1 failed"

    # 示例 2
    assert sol.uniquePaths(3, 2) == 3, "Test 2 failed"

    # 示例 3
    assert sol.uniquePaths(7, 3) == 28, "Test 3 failed"

    # 示例 4
    assert sol.uniquePaths(3, 3) == 6, "Test 4 failed"

    # 边界：1x1
    assert sol.uniquePaths(1, 1) == 1, "Test 1x1 failed"

    # 边界：1xn
    assert sol.uniquePaths(1, 100) == 1, "Test 1xn failed"

    # 边界：mx1
    assert sol.uniquePaths(100, 1) == 1, "Test mx1 failed"

    # 边界：2x2
    assert sol.uniquePaths(2, 2) == 2, "Test 2x2 failed"

    print("All tests passed for LC 62 - Unique Paths")


if __name__ == "__main__":
    test_unique_paths()
