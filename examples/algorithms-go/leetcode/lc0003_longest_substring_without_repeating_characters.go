// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
package leetcode

// LengthOfLongestSubstring 计算不含重复字符的最长子串长度。
//
// 形式化规约：
//   Pre: s 为字符串，长度 ∈ [0, 5*10^4]。
//   Post: 返回 max_{0 ≤ l ≤ r < n} (r-l+1)，其中 s[l..r] 不含重复字符。
//
// 窗口不变式 WindowInvariant(left, right)：
//   s[left..right] 中所有字符均唯一。
//
//   维护：
//   - 扩展 right：考察 s[right]。
//     若 s[right] 在窗口中（上次出现位置 ≥ left），将 left 移动到上次出现位置+1。
//   - 更新 s[right] 的最后出现位置。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(min(m, n))，m 为字符集大小（ASCII 下为 O(1)）
//
// 证明要点：
//   - 不遗漏最优解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
func LengthOfLongestSubstring(s string) int {
	// ASCII 字符集，可用大小 128 的数组记录最后出现位置
	lastPos := make([]int, 128)
	for i := range lastPos {
		lastPos[i] = -1
	}

	maxLen := 0
	left := 0

	for right, ch := range s {
		idx := int(ch)
		if lastPos[idx] >= left {
			left = lastPos[idx] + 1
		}
		lastPos[idx] = right
		if right-left+1 > maxLen {
			maxLen = right - left + 1
		}
	}

	return maxLen
}
