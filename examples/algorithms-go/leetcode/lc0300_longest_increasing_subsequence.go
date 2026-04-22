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
//   DP 版本: dp[i] 表示以 nums[i] 结尾的最长递增子序列长度
//   二分优化: 维护数组 tails[k] 表示长度为 k+1 的递增子序列的最小末尾值
//
// 复杂度:
//   DP 时间: O(n^2), 空间: O(n)
//   二分时间: O(n log n), 空间: O(n)

package leetcode

import "sort"

// LengthOfLISDP 动态规划版本 O(n^2)
func LengthOfLISDP(nums []int) int {
	n := len(nums)
	if n == 0 {
		return 0
	}
	dp := make([]int, n)
	maxLen := 1
	for i := 0; i < n; i++ {
		dp[i] = 1
		for j := 0; j < i; j++ {
			if nums[j] < nums[i] && dp[j]+1 > dp[i] {
				dp[i] = dp[j] + 1
			}
		}
		if dp[i] > maxLen {
			maxLen = dp[i]
		}
	}
	return maxLen
}

// LengthOfLISBinary 二分优化版本 O(n log n)
func LengthOfLISBinary(nums []int) int {
	if len(nums) == 0 {
		return 0
	}

	tails := make([]int, 0, len(nums))
	for _, num := range nums {
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
	if LengthOfLISBinary([]int{10, 9, 2, 5, 3, 7, 101, 18}) != 4 {
		panic("Test 1 failed")
	}
	// 示例 2
	if LengthOfLISBinary([]int{0, 1, 0, 3, 2, 3}) != 4 {
		panic("Test 2 failed")
	}
	// 示例 3
	if LengthOfLISBinary([]int{7, 7, 7, 7, 7, 7, 7}) != 1 {
		panic("Test 3 failed")
	}
	// 边界: 空数组
	if LengthOfLISBinary([]int{}) != 0 {
		panic("Test empty failed")
	}
	// 边界: 严格递增
	if LengthOfLISBinary([]int{1, 2, 3, 4, 5}) != 5 {
		panic("Test ascending failed")
	}
}
