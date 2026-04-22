// LeetCode 191. Number of 1 Bits
// 链接: https://leetcode.com/problems/number-of-1-bits/
// 难度: Easy
//
// 算法: Brian Kernighan 算法
// 时间复杂度: O(k)，k = 1 的个数
// 空间复杂度: O(1)
//
// 数学基础: n & (n-1) 清除 n 的最低设置位。
// 证明: 设 n = (A 1 0^t)_2，则 n-1 = (A 0 1^t)_2，
//       n & (n-1) = (A 0 0^t)_2，恰好清除最低设置位。

package leetcode

// HammingWeight 返回 n 的二进制表示中 1 的个数。
func HammingWeight(n uint32) int {
	count := 0
	for n != 0 {
		n &= n - 1 // 清除最低设置位
		count++
	}
	return count
}
