// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
package leetcode

import "math"

// MinWindow 找出 s 中涵盖 t 所有字符的最小子串。
//
// 形式化规约：
//   Pre: s, t 由大写/小写英文字母组成；len(s), len(t) ∈ [1, 10^5]。
//   Post: 返回 s 的最短子串 substr，使得 t 中每个字符在 substr 中出现次数
//         均不少于在 t 中的出现次数；若不存在返回空字符串。
//
// 算法框架：
//   滑动窗口 + 双哈希表（need 和 window），用 valid 记录满足需求的字符种类数。
//
// 窗口不变式：
//   window 准确记录 s[left..right] 中各字符出现次数。
//   valid 等于 window[ch] ≥ need[ch] 的字符种类数（只考虑 need 中的字符）。
//
//   维护：
//   - 扩展 right：将 s[right] 加入 window，若 window[ch] == need[ch]，valid++。
//   - 当 valid == len(need) 时，尝试收缩 left，更新最小窗口，
//     移出 s[left]，若 window[ch] < need[ch]，valid--。
//
// 复杂度：
//   时间复杂度: O(|s| + |t|)
//   空间复杂度: O(|Σ|) = O(1)（字符集大小为 52）
//
// 证明要点：
//   - 窗口收缩正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
func MinWindow(s string, t string) string {
	if len(s) == 0 || len(t) == 0 {
		return ""
	}

	// need 记录 t 中各字符需求量
	need := make(map[byte]int)
	for i := 0; i < len(t); i++ {
		need[t[i]]++
	}

	window := make(map[byte]int)
	valid := 0
	left := 0
	start := 0
	minLen := math.MaxInt32

	for right := 0; right < len(s); right++ {
		ch := s[right]
		window[ch]++
		if cnt, ok := need[ch]; ok && window[ch] == cnt {
			valid++
		}

		for valid == len(need) {
			if right-left+1 < minLen {
				minLen = right - left + 1
				start = left
			}

			leftCh := s[left]
			window[leftCh]--
			if cnt, ok := need[leftCh]; ok && window[leftCh] < cnt {
				valid--
			}
			left++
		}
	}

	if minLen == math.MaxInt32 {
		return ""
	}
	return s[start : start+minLen]
}
