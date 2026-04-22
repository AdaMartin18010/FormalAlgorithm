// LeetCode 79. Word Search
// 链接: https://leetcode.com/problems/word-search/
// 难度: Medium
//
// 算法: DFS + 回溯
// 时间复杂度: O(m * n * 3^k)，k = len(word)
// 空间复杂度: O(k)

package leetcode

// Exist 判断 board 中是否存在 word 的路径。
func Exist(board [][]byte, word string) bool {
	m := len(board)
	if m == 0 {
		return false
	}
	n := len(board[0])
	visited := make([][]bool, m)
	for i := range visited {
		visited[i] = make([]bool, n)
	}

	var dfs func(r, c, idx int) bool
	dfs = func(r, c, idx int) bool {
		if idx == len(word) {
			return true
		}
		if r < 0 || r >= m || c < 0 || c >= n {
			return false
		}
		if visited[r][c] || board[r][c] != word[idx] {
			return false
		}

		// 做选择: 标记访问
		visited[r][c] = true
		// 向四个方向递归
		found := dfs(r+1, c, idx+1) || dfs(r-1, c, idx+1) ||
			dfs(r, c+1, idx+1) || dfs(r, c-1, idx+1)
		// 撤销选择: 恢复访问标记（关键！）
		visited[r][c] = false
		return found
	}

	for r := 0; r < m; r++ {
		for c := 0; c < n; c++ {
			if board[r][c] == word[0] && dfs(r, c, 0) {
				return true
			}
		}
	}
	return false
}
