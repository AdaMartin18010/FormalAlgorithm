package leetcode

// SearchMatrix 搜索二维矩阵 II
// 从右上角开始搜索：
// - 若 target > matrix[row][col]，说明当前行所有元素都小于 target，row++
// - 若 target < matrix[row][col]，说明当前列所有元素都大于 target，col--
// 时间复杂度 O(m+n)，空间复杂度 O(1)
func SearchMatrix(matrix [][]int, target int) bool {
	if len(matrix) == 0 || len(matrix[0]) == 0 {
		return false
	}
	m, n := len(matrix), len(matrix[0])
	row, col := 0, n-1
	for row < m && col >= 0 {
		if matrix[row][col] == target {
			return true
		} else if matrix[row][col] < target {
			row++
		} else {
			col--
		}
	}
	return false
}
