// LeetCode 46. Permutations
// 链接: https://leetcode.com/problems/permutations/
// 难度: Medium
//
// 算法: 回溯（排列树）
// 时间复杂度: O(n * n!)
// 空间复杂度: O(n)

package leetcode

// Permute 生成 nums 的所有全排列。
//
// 形式化规约:
// - 前置条件: nums 为无重复元素的整数数组
// - 后置条件: 返回 nums 的所有 n! 个排列，无重复
func Permute(nums []int) [][]int {
	n := len(nums)
	res := make([][]int, 0, factorial(n))
	path := make([]int, 0, n)
	used := make([]bool, n)

	var backtrack func(k int)
	backtrack = func(k int) {
		if k == n {
			// 找到一个完整解，复制路径
			tmp := make([]int, n)
			copy(tmp, path)
			res = append(res, tmp)
			return
		}

		for i := 0; i < n; i++ {
			if used[i] {
				continue
			}
			// 做选择
			used[i] = true
			path = append(path, nums[i])
			// 递归
			backtrack(k + 1)
			// 撤销选择
			path = path[:len(path)-1]
			used[i] = false
		}
	}

	backtrack(0)
	return res
}

// factorial 计算阶乘（用于预分配结果容量）。
func factorial(n int) int {
	if n <= 1 {
		return 1
	}
	res := 1
	for i := 2; i <= n; i++ {
		res *= i
	}
	return res
}
