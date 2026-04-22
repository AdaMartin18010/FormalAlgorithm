// LeetCode 300. Longest Increasing Subsequence
// 链接: https://leetcode.com/problems/longest-increasing-subsequence/
// 难度: Medium
//
// 题目描述:
// 给你一个整数数组 nums，找到其中最长严格递增子序列的长度。
//
// 形式化规约:
//   输入: 数组 nums ∈ Z^n
//   输出: 最长严格递增子序列（LIS）的长度
//
// 最优解思路:
//   二分优化：维护数组 tails[k] 表示长度为 k+1 的递增子序列的最小末尾值。
//   对 nums[i] 在 tails 中二分查找替换位置（lower_bound）。
//
// 复杂度:
//   时间: O(n log n)
//   空间: O(n)
//
// 正确性要点:
//   1. tails 数组是严格递增的，因此可以二分查找
//   2. 二分优化只能求长度，不能直接输出具体序列
//   3. lower_bound 找到第一个 >= nums[i] 的位置并替换

package leetcode

import "sort"

func lengthOfLIS(nums []int) int {
	if len(nums) == 0 {
		return 0
	}

	tails := make([]int, 0, len(nums))
	for _, num := range nums {
		// 在 tails 中找到第一个 >= num 的位置
		idx := sort.Search(len(tails), func(i int) bool {
			return tails[i] >= num
		})
		if idx == len(tails) {
			tails = append(tails, num)
		} else {
			tails[idx] = num
		}
	}

	return len(tails)
}

// TestLIS 测试最长递增子序列函数
func TestLIS() {
	// 示例 1
	if lengthOfLIS([]int{10, 9, 2, 5, 3, 7, 101, 18}) != 4 {
		panic("Test 1 failed")
	}
	// 示例 2
	if lengthOfLIS([]int{0, 1, 0, 3, 2, 3}) != 4 {
		panic("Test 2 failed")
	}
	// 示例 3
	if lengthOfLIS([]int{7, 7, 7, 7, 7, 7, 7}) != 1 {
		panic("Test 3 failed")
	}
	// 边界: 空数组
	if lengthOfLIS([]int{}) != 0 {
		panic("Test empty failed")
	}
	// 边界: 严格递增
	if lengthOfLIS([]int{1, 2, 3, 4, 5}) != 5 {
		panic("Test ascending failed")
	}
}
