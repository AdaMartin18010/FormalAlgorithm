// LeetCode 62. Unique Paths
// https://leetcode.com/problems/unique-paths/
//
// Problem: A robot is located at the top-left corner of a m x n grid.
// The robot can only move either down or right at any point in time.
// The robot is trying to reach the bottom-right corner of the grid.
// How many possible unique paths are there?
//
// Formal specification:
// - Pre: 1 <= m, n <= 100
// - Post: number of unique paths from (0,0) to (m-1,n-1)
//
// Algorithm: Combinatorics. Total steps = m+n-2, choose m-1 down steps.
//   C(m+n-2, min(m-1, n-1)) to minimize iterations.
// Time: O(min(m,n)), Space: O(1).

package leetcode

// UniquePaths 计算从网格左上角到右下角的不同路径总数（只能右或下）。
// 使用组合数学：C(m+n-2, min(m-1, n-1))。
func UniquePaths(m, n int) int {
	total := m + n - 2
	k := m - 1
	if n-1 < k {
		k = n - 1
	}

	result := 1
	for i := 0; i < k; i++ {
		result = result * (total - i) / (i + 1)
	}
	return result
}
