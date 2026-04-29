// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
package leetcode

// CanJump 判断是否能到达最后一个下标。
//
// 形式化规约：
//   Pre: nums 为非负整数数组，len(nums) >= 1。
//   Post: 若能到达最后一个位置，返回 true；否则返回 false。
//
// 核心思路：
//   贪心策略：维护最远可达位置 reach。
//   若当前位置 i <= reach，则更新 reach = max(reach, i + nums[i])。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
func CanJump(nums []int) bool {
	reach := 0
	n := len(nums)

	for i := 0; i < n; i++ {
		if i > reach {
			return false
		}
		if i+nums[i] > reach {
			reach = i + nums[i]
		}
		if reach >= n-1 {
			return true
		}
	}

	return true
}
