// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
package leetcode

// SubarraySum 计算和为 k 的连续子数组的个数。
//
// 形式化规约：
//   Pre: nums 为整数数组，len(nums) >= 1。
//   Post: 返回和恰好等于 k 的连续子数组的数量。
//
// 核心思路：
//   前缀和 + 哈希表。S(l, r) = prefix[r+1] - prefix[l] = k
//   ⇔ prefix[r+1] = prefix[l] + k。
//   遍历过程中维护已出现前缀和的频次映射。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(n)
func SubarraySum(nums []int, k int) int {
	count := 0
	prefix := 0
	freq := make(map[int]int)
	freq[0] = 1 // 空前缀的和为 0，出现 1 次

	for _, num := range nums {
		prefix += num
		if v, ok := freq[prefix-k]; ok {
			count += v
		}
		freq[prefix]++
	}

	return count
}
