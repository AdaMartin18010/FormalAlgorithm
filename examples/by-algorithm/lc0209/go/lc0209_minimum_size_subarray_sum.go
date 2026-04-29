// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
package leetcode

import "math"

// MinSubArrayLen 找出和大于等于 target 的最短连续子数组长度。
//
// 形式化规约：
//   Pre: nums 为正整数数组，长度 ∈ [1, 10^5]；target ∈ [1, 10^9]。
//   Post: 返回 min_{0 ≤ l ≤ r < n, sum(nums[l..r]) ≥ target} (r-l+1)，
//         若不存在则返回 0。
//
// 窗口不变式 WindowInvariant(left, right)：
//   window_sum = sum(nums[left..right])。
//
//   关键引理（收缩的正确性）：
//   若当前窗口 [left, right] 满足 window_sum ≥ target，
//   则对于任何 left' > left，窗口 [left', right] 的长度更小。
//   若仍满足和 ≥ target，则找到了更优（更短）的候选解。
//   因此可安全将 left 右移以探索更短窗口。
//
// 复杂度：
//   时间复杂度: O(n) — 摊还分析：每个元素最多加入和移出窗口各一次。
//   空间复杂度: O(1)
//
// 证明要点：
//   - 窗口收缩正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
func MinSubArrayLen(target int, nums []int) int {
	n := len(nums)
	minLen := math.MaxInt32
	left := 0
	windowSum := 0

	for right := 0; right < n; right++ {
		windowSum += nums[right]
		for windowSum >= target {
			if right-left+1 < minLen {
				minLen = right - left + 1
			}
			windowSum -= nums[left]
			left++
		}
	}

	if minLen == math.MaxInt32 {
		return 0
	}
	return minLen
}
