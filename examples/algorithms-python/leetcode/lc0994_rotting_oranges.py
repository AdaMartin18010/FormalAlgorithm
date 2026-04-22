"""
LeetCode 994. Rotting Oranges
链接: https://leetcode.com/problems/rotting-oranges/
难度: Medium

算法: 多源 BFS
时间复杂度: O(m * n)
空间复杂度: O(m * n)
"""

from typing import List
from collections import deque


class Solution:
    def orangesRotting(self, grid: List[List[int]]) -> int:
        """
        返回腐烂所有新鲜橘子所需的最短分钟数。
        
        形式化规约:
        - 前置条件: grid 为 m×n 的矩阵，元素 ∈ {0, 1, 2}
        - 后置条件: 返回最短时间，若无法全部腐烂则返回 -1
        
        算法: 多源 BFS。将所有初始腐烂橘子作为第 0 层源点同时入队，
        每分钟（BFS 一层）向四个方向扩散。BFS 层数 = 最短分钟数。
        """
        m, n = len(grid), len(grid[0])
        queue = deque()
        fresh_count = 0
        
        # 初始化: 收集所有腐烂橘子（多源）和统计新鲜橘子
        for r in range(m):
            for c in range(n):
                if grid[r][c] == 2:
                    queue.append((r, c, 0))  # (row, col, time)
                elif grid[r][c] == 1:
                    fresh_count += 1
        
        if fresh_count == 0:
            return 0
        
        minutes = 0
        dirs = [(0, 1), (0, -1), (1, 0), (-1, 0)]
        
        # 多源 BFS
        while queue:
            r, c, t = queue.popleft()
            minutes = max(minutes, t)
            
            for dr, dc in dirs:
                nr, nc = r + dr, c + dc
                if 0 <= nr < m and 0 <= nc < n and grid[nr][nc] == 1:
                    grid[nr][nc] = 2  # 腐烂
                    fresh_count -= 1
                    queue.append((nr, nc, t + 1))
        
        return minutes if fresh_count == 0 else -1


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1
    grid1 = [[2, 1, 1], [1, 1, 0], [0, 1, 1]]
    res1 = sol.orangesRotting(grid1)
    print(f"Test 1: {res1} (expected: 4)")
    assert res1 == 4
    
    # 测试用例 2: 有橘子无法腐烂
    grid2 = [[2, 1, 1], [0, 1, 1], [1, 0, 1]]
    res2 = sol.orangesRotting(grid2)
    print(f"Test 2: {res2} (expected: -1)")
    assert res2 == -1
    
    # 测试用例 3: 没有新鲜橘子
    grid3 = [[0, 2]]
    res3 = sol.orangesRotting(grid3)
    print(f"Test 3: {res3} (expected: 0)")
    assert res3 == 0
    
    print("\nAll tests passed!")
