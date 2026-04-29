// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
package leetcode

// CheckSubarraySum 检查是否存在长度至少为 2 且和可被 k 整除的连续子数组。
//
// 形式化规约：
//   Pre: nums 为整数数组，len(nums) >= 1；k 为整数。
//   Post: 若存在长度 >= 2 且和 % k == 0 的连续子数组，返回 true；否则返回 false。
//
// 核心思路：
//   前缀和 + 同余定理。
//   k | S(l, r) ⇔ prefix[r+1] ≡ prefix[l] (mod k)。
//   维护哈希表记录每个余数最早出现的位置。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(min(n, |k|))
func CheckSubarraySum(nums []int, k int) bool {
	n := len(nums)
	if n < 2 {
		return false
	}

	// k = 0 特判
	if k == 0 {
		for i := 0; i < n-1; i++ {
			if nums[i] == 0 && nums[i+1] == 0 {
				return true
			}
		}
		return false
	}

	prefix := 0
	firstOccurrence := make(map[int]int)
	firstOccurrence[0] = 0 // prefix[0] = 0 出现在位置 0

	for i := 0; i < n; i++ {
		prefix = ((prefix + nums[i]) % k + k) % k // 处理负数
		if pos, ok := firstOccurrence[prefix]; ok {
			if i+1-pos >= 2 {
				return true
			}
		} else {
			firstOccurrence[prefix] = i + 1
		}
	}

	return false
}
