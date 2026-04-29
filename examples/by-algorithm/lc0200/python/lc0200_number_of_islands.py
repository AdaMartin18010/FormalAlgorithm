"""
LeetCode 200. Number of Islands
链接: https://leetcode.com/problems/number-of-islands/
难度: Medium

题目描述:
给你一个由 '1'（陆地）和 '0'（水）组成的的二维网格，请你计算网格中岛屿的数量。
岛屿总是被水包围，并且每座岛屿只能由水平方向和/或竖直方向上相邻的陆地连接形成。

形式化规约:
  输入: m × n 网格 grid，grid[i][j] ∈ {'0', '1'}
  输出: 岛屿数量（由 '1' 组成的四连通区域数）

最优解思路:
  DFS：遍历网格，遇到 '1' 时启动 DFS 将该岛屿所有 '1' 标记为 '0'（访问标记），岛屿计数 +1。

复杂度:
  时间: O(mn)
  空间: O(mn) 最坏（递归栈）

正确性要点:
  1. 每个陆地格子恰好被访问一次（访问后立即标记）
  2. DFS 的递归深度最坏为 O(mn)，极大网格需考虑栈溢出，可改用 BFS
  3. 四个方向的邻居搜索注意边界检查
"""

from typing import List


class Solution:
    def numIslands(self, grid: List[List[str]]) -> int:
        """
        DFS 标记法。时间 O(mn)，空间 O(mn)。
        """
        if not grid or not grid[0]:
            return 0

        m, n = len(grid), len(grid[0])
        count = 0

        def dfs(i: int, j: int) -> None:
            if i < 0 or i >= m or j < 0 or j >= n or grid[i][j] == '0':
                return
            grid[i][j] = '0'  # 标记为已访问
            dfs(i + 1, j)
            dfs(i - 1, j)
            dfs(i, j + 1)
            dfs(i, j - 1)

        for i in range(m):
            for j in range(n):
                if grid[i][j] == '1':
                    count += 1
                    dfs(i, j)

        return count

    def numIslandsBFS(self, grid: List[List[str]]) -> int:
        """
        BFS 标记法。时间 O(mn)，空间 O(min(m, n))。
        适合极大网格，避免递归栈溢出。
        """
        if not grid or not grid[0]:
            return 0

        from collections import deque

        m, n = len(grid), len(grid[0])
        count = 0
        dirs = [(1, 0), (-1, 0), (0, 1), (0, -1)]

        for i in range(m):
            for j in range(n):
                if grid[i][j] == '1':
                    count += 1
                    queue = deque([(i, j)])
                    grid[i][j] = '0'
                    while queue:
                        x, y = queue.popleft()
                        for dx, dy in dirs:
                            nx, ny = x + dx, y + dy
                            if 0 <= nx < m and 0 <= ny < n and grid[nx][ny] == '1':
                                grid[nx][ny] = '0'
                                queue.append((nx, ny))

        return count


def test_num_islands():
    sol = Solution()
    # 示例 1
    grid1 = [
        ["1", "1", "1", "1", "0"],
        ["1", "1", "0", "1", "0"],
        ["1", "1", "0", "0", "0"],
        ["0", "0", "0", "0", "0"]
    ]
    assert sol.numIslands([row[:] for row in grid1]) == 1, "Test 1 DFS failed"
    assert sol.numIslandsBFS([row[:] for row in grid1]) == 1, "Test 1 BFS failed"
    # 示例 2
    grid2 = [
        ["1", "1", "0", "0", "0"],
        ["1", "1", "0", "0", "0"],
        ["0", "0", "1", "0", "0"],
        ["0", "0", "0", "1", "1"]
    ]
    assert sol.numIslands([row[:] for row in grid2]) == 3, "Test 2 DFS failed"
    assert sol.numIslandsBFS([row[:] for row in grid2]) == 3, "Test 2 BFS failed"
    # 边界: 空网格
    assert sol.numIslands([]) == 0, "Test empty failed"
    print("All tests passed for LC 200 - Number of Islands")


if __name__ == "__main__":
    test_num_islands()
