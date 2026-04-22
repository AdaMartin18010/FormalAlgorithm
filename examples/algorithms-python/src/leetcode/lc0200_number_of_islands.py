"""LeetCode 200. 岛屿数量 — Python 实现

给定一个由 '1'（陆地）和 '0'（水）组成的二维网格，计算岛屿数量。

岛屿由相邻的陆地（上下左右）连接而成。

对标: LeetCode 200 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md
"""

from typing import List
from collections import deque


def num_islands(grid: List[List[str]]) -> int:
    """返回网格中岛屿的数量（BFS 版本）。

    前置条件 (Pre):
        - grid 为 m x n 的二维列表，元素为 '0' 或 '1'。
        - 1 <= m, n <= 300。

    后置条件 (Post):
        - 返回岛屿数量（连通的 '1' 组件数）。

    BFS 不变式 (Invariant):
        每次从一个未访问的陆地 '1' 开始 BFS，会将该陆地所在岛屿的所有陆地标记为已访问（改为 '0'）。
        因此外层循环每次发现 '1' 时，必然是一个新岛屿。

    复杂度:
        时间复杂度: O(m * n) — 每个单元格最多被访问一次。
        空间复杂度: O(min(m, n)) — BFS 队列最大长度，最坏情况下为网格短边的长度。

    证明要点:
        - 完备性：BFS 从任意陆地出发，会访问该岛屿所有可达陆地（上下四连通）。
        - 正确计数：每个岛屿有且仅有一个 BFS 起点（第一个发现的未访问陆地），因此计数准确。

    Args:
        grid: 由 '0' 和 '1' 组成的二维网格。

    Returns:
        岛屿数量。
    """
    if not grid or not grid[0]:
        return 0

    m, n = len(grid), len(grid[0])
    count = 0
    directions = [(0, 1), (0, -1), (1, 0), (-1, 0)]

    def bfs(r: int, c: int) -> None:
        queue = deque([(r, c)])
        grid[r][c] = "0"
        while queue:
            cr, cc = queue.popleft()
            for dr, dc in directions:
                nr, nc = cr + dr, cc + dc
                if 0 <= nr < m and 0 <= nc < n and grid[nr][nc] == "1":
                    grid[nr][nc] = "0"
                    queue.append((nr, nc))

    for r in range(m):
        for c in range(n):
            if grid[r][c] == "1":
                count += 1
                bfs(r, c)

    return count


def num_islands_dfs(grid: List[List[str]]) -> int:
    """返回网格中岛屿的数量（DFS 版本）。

    复杂度与正确性同 BFS 版本，空间复杂度为 O(m * n)（递归栈）。
    """
    if not grid or not grid[0]:
        return 0

    m, n = len(grid), len(grid[0])
    count = 0

    def dfs(r: int, c: int) -> None:
        if r < 0 or r >= m or c < 0 or c >= n or grid[r][c] == "0":
            return
        grid[r][c] = "0"
        dfs(r + 1, c)
        dfs(r - 1, c)
        dfs(r, c + 1)
        dfs(r, c - 1)

    for r in range(m):
        for c in range(n):
            if grid[r][c] == "1":
                count += 1
                dfs(r, c)

    return count


if __name__ == "__main__":
    # LeetCode 官方示例
    grid1 = [
        ["1", "1", "1", "1", "0"],
        ["1", "1", "0", "1", "0"],
        ["1", "1", "0", "0", "0"],
        ["0", "0", "0", "0", "0"],
    ]
    assert num_islands([row[:] for row in grid1]) == 1, "Example 1 BFS failed"
    assert num_islands_dfs([row[:] for row in grid1]) == 1, "Example 1 DFS failed"

    grid2 = [
        ["1", "1", "0", "0", "0"],
        ["1", "1", "0", "0", "0"],
        ["0", "0", "1", "0", "0"],
        ["0", "0", "0", "1", "1"],
    ]
    assert num_islands([row[:] for row in grid2]) == 3, "Example 2 BFS failed"
    assert num_islands_dfs([row[:] for row in grid2]) == 3, "Example 2 DFS failed"

    # 边界条件
    assert num_islands([["0"]]) == 0, "Single water"
    assert num_islands([["1"]]) == 1, "Single land"
    assert num_islands([]) == 0, "Empty grid"

    print("All tests passed.")
