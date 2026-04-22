// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
package leetcode

// SortArray 使用归并排序将数组升序排列。
//
// 形式化规约：
//   Pre: nums 为整数数组。
//   Post: 返回 nums 的一个非降序排列。
//
// 核心思路：
//   分治归并排序：二分分解 + 递归排序 + 线性合并。
//
// 复杂度：
//   时间复杂度: O(n log n)
//   空间复杂度: O(n)
func SortArray(nums []int) []int {
	n := len(nums)
	if n <= 1 {
		result := make([]int, n)
		copy(result, nums)
		return result
	}

	mid := n / 2
	left := SortArray(nums[:mid])
	right := SortArray(nums[mid:])

	return merge(left, right)
}

func merge(left, right []int) []int {
	result := make([]int, 0, len(left)+len(right))
	i, j := 0, 0

	for i < len(left) && j < len(right) {
		if left[i] <= right[j] {
			result = append(result, left[i])
			i++
		} else {
			result = append(result, right[j])
			j++
		}
	}

	for i < len(left) {
		result = append(result, left[i])
		i++
	}
	for j < len(right) {
		result = append(result, right[j])
		j++
	}

	return result
}
