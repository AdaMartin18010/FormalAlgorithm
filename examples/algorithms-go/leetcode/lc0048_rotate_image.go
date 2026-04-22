// LeetCode 48. Rotate Image
// https://leetcode.com/problems/rotate-image/
//
// Problem: You are given an n x n 2D matrix representing an image, rotate the image by 90 degrees (clockwise).
// You have to rotate the image in-place, which means you have to modify the input 2D matrix directly.
//
// Formal specification:
// - Pre: matrix is n x n, n >= 1
// - Post: matrix is rotated 90 degrees clockwise in-place
//
// Algorithm: Transpose then horizontal flip.
//   Transpose swaps matrix[i][j] with matrix[j][i].
//   Horizontal flip swaps matrix[i][j] with matrix[i][n-1-j].
//   Combined: (i,j) -> (j,i) -> (j,n-1-i).
// Time: O(n^2), Space: O(1).

package leetcode

// Rotate 原地顺时针旋转 n × n 矩阵 90 度。
// 先沿主对角线转置，再对每行进行水平翻转。
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
