// LeetCode 994. Rotting Oranges
// 链接: https://leetcode.com/problems/rotting-oranges/
// 难度: Medium
//
// 算法: 多源 BFS
// 时间复杂度: O(m * n)
// 空间复杂度: O(m * n)

package leetcode

import "container/list"

// OrangesRotting 返回腐烂所有新鲜橘子所需的最短分钟数。
func OrangesRotting(grid [][]int) int {
	m := len(grid)
	if m == 0 {
		return 0
	}
	n := len(grid[0])

	queue := list.New()
	freshCount := 0

	// 初始化: 将所有腐烂橘子入队，统计新鲜橘子
	for r := 0; r < m; r++ {
		for c := 0; c < n; c++ {
			switch grid[r][c] {
			case 2:
				queue.PushBack([3]int{r, c, 0})
			case 1:
				freshCount++
			}
		}
	}

	if freshCount == 0 {
		return 0
	}

	minutes := 0
	dirs := [][2]int{{0, 1}, {0, -1}, {1, 0}, {-1, 0}}

	// 多源 BFS
	for queue.Len() > 0 {
		elem := queue.Front()
		queue.Remove(elem)
		cell := elem.Value.([3]int)
		r, c, t := cell[0], cell[1], cell[2]

		if t > minutes {
			minutes = t
		}

		for _, d := range dirs {
			nr, nc := r+d[0], c+d[1]
			if nr >= 0 && nr < m && nc >= 0 && nc < n && grid[nr][nc] == 1 {
				grid[nr][nc] = 2
				freshCount--
				queue.PushBack([3]int{nr, nc, t + 1})
			}
		}
	}

	if freshCount == 0 {
		return minutes
	}
	return -1
}
