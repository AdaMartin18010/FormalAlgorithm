package leetcode

// LeetCode 48. 旋转图像
//
// 给定一个 n × n 的二维矩阵 matrix，将矩阵顺时针旋转 90 度（原地）。
//
// 思路：两步法（转置 + 水平翻转）
// 1. 转置矩阵：沿主对角线交换元素，matrix[i][j] <-> matrix[j][i]。
// 2. 水平翻转每一行：matrix[i][j] <-> matrix[i][n-1-j]。
//
// 时间复杂度：O(n^2)，空间复杂度：O(1)。

// Rotate 原地顺时针旋转 n × n 矩阵 90 度。
func Rotate(matrix [][]int) {
	n := len(matrix)
	if n <= 1 {
		return
	}

	// 步骤1：转置（沿主对角线交换）
	for i := 0; i < n; i++ {
		for j := i + 1; j < n; j++ {
			matrix[i][j], matrix[j][i] = matrix[j][i], matrix[i][j]
		}
	}

	// 步骤2：水平翻转（每行左右对称交换）
	for i := 0; i < n; i++ {
		for j := 0; j < n/2; j++ {
			matrix[i][j], matrix[i][n-1-j] = matrix[i][n-1-j], matrix[i][j]
		}
	}
}
