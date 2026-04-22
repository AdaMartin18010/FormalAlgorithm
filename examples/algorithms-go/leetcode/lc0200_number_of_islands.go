// LeetCode 200. Number of Islands
// 链接: https://leetcode.com/problems/number-of-islands/
// 难度: Medium
//
// 题目描述:
// 给你一个由 '1'（陆地）和 '0'（水）组成的的二维网格，请你计算网格中岛屿的数量。
//
// 形式化规约:
//   输入: m × n 网格 grid，grid[i][j] ∈ {'0', '1'}
//   输出: 岛屿数量（由 '1' 组成的四连通区域数）
//
// 最优解思路:
//   DFS Flood Fill：遍历网格，遇到 '1' 时启动 DFS 将该岛屿所有 '1' 标记为 '0'，岛屿计数 +1。
//
// 复杂度:
//   时间: O(mn)
//   空间: O(mn) 最坏（递归栈）

package leetcode

func numIslands(grid [][]byte) int {
	if len(grid) == 0 || len(grid[0]) == 0 {
		return 0
	}
	m, n := len(grid), len(grid[0])
	count := 0

	var dfs func(r, c int)
	dfs = func(r, c int) {
		if r < 0 || r >= m || c < 0 || c >= n || grid[r][c] == '0' {
			return
		}
		grid[r][c] = '0' // 标记为已访问
		dfs(r+1, c)
		dfs(r-1, c)
		dfs(r, c+1)
		dfs(r, c-1)
	}

	for i := 0; i < m; i++ {
		for j := 0; j < n; j++ {
			if grid[i][j] == '1' {
				count++
				dfs(i, j)
			}
		}
	}
	return count
}

// TestNumIslands 测试岛屿数量函数
func TestNumIslands() {
	// 示例 1
	grid1 := [][]byte{
		{'1', '1', '1', '1', '0'},
		{'1', '1', '0', '1', '0'},
		{'1', '1', '0', '0', '0'},
		{'0', '0', '0', '0', '0'},
	}
	if numIslands(grid1) != 1 {
		panic("Test 1 failed")
	}

	// 示例 2
	grid2 := [][]byte{
		{'1', '1', '0', '0', '0'},
		{'1', '1', '0', '0', '0'},
		{'0', '0', '1', '0', '0'},
		{'0', '0', '0', '1', '1'},
	}
	if numIslands(grid2) != 3 {
		panic("Test 2 failed")
	}

	// 边界: 全水
	grid3 := [][]byte{{'0'}}
	if numIslands(grid3) != 0 {
		panic("Test 3 failed")
	}
}
