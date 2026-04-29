"""LeetCode 994. 腐烂的橘子 — Python 实现

在给定的网格中，0 表示空单元格，1 表示新鲜橘子，2 表示腐烂橘子。每分钟，腐烂橘子会使上下左右相邻的新鲜橘子腐烂。

返回直到没有新鲜橘子为止所需的最小分钟数，若无法使所有橘子腐烂则返回 -1。

对标: LeetCode 994 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md
"""

from typing import List
from collections import deque


def oranges_rotting(grid: List[List[int]]) -> int:
    """返回所有新鲜橘子腐烂所需的最小分钟数。

    前置条件 (Pre):
        - grid 为 m x n 的二维列表，元素为 0、1 或 2。
        - 1 <= m, n <= 10。

    后置条件 (Post):
        - 返回最小分钟数，若存在无法腐烂的新鲜橘子则返回 -1。

    BFS 层级不变式 (Layer Invariant):
        第 t 分钟时，队列中恰好包含第 t 分钟新腐烂的所有橘子。
        即 BFS 第 d 层对应第 d 分钟新腐烂的橘子集合。

    复杂度:
        时间复杂度: O(m * n) — 每个单元格最多入队一次。
        空间复杂度: O(m * n) — 队列最多包含所有单元格。

    证明要点:
        - 多源 BFS 的正确性：所有初始腐烂橘子同时开始扩散，BFS 层数即为时间步。
        - 最短性：BFS 保证每个新鲜橘子被最早到达的腐烂源腐烂，即最小时间。
        - 终止判断：BFS 结束后检查是否还有新鲜橘子剩余。

    Args:
        grid: m x n 的网格，0 为空，1 为新鲜，2 为腐烂。

    Returns:
        最小分钟数，无法全部腐烂则返回 -1。
    """
    if not grid or not grid[0]:
        return 0

    m, n = len(grid), len(grid[0])
    queue = deque()
    fresh = 0

    # 初始化：收集所有腐烂橘子，统计新鲜橘子
    for r in range(m):
        for c in range(n):
            if grid[r][c] == 2:
                queue.append((r, c, 0))
            elif grid[r][c] == 1:
                fresh += 1

    if fresh == 0:
        return 0

    minutes = 0
    directions = [(0, 1), (0, -1), (1, 0), (-1, 0)]

    while queue:
        r, c, t = queue.popleft()
        minutes = max(minutes, t)
        for dr, dc in directions:
            nr, nc = r + dr, c + dc
            if 0 <= nr < m and 0 <= nc < n and grid[nr][nc] == 1:
                grid[nr][nc] = 2
                fresh -= 1
                queue.append((nr, nc, t + 1))

    return minutes if fresh == 0 else -1


if __name__ == "__main__":
    # LeetCode 官方示例
    assert oranges_rotting([[2, 1, 1], [1, 1, 0], [0, 1, 1]]) == 4, "Example 1 failed"
    assert oranges_rotting([[2, 1, 1], [0, 1, 1], [1, 0, 1]]) == -1, "Example 2 failed"
    assert oranges_rotting([[0, 2]]) == 0, "Example 3 failed"

    # 边界条件
    assert oranges_rotting([[1]]) == -1, "Single fresh orange"
    assert oranges_rotting([[2]]) == 0, "Single rotten orange"
    assert oranges_rotting([[0]]) == 0, "Single empty cell"

    print("All tests passed.")
