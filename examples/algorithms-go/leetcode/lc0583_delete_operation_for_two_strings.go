package leetcode

// LeetCode 583. 两个字符串的删除操作
//
// 给定两个单词 word1 和 word2，找到使得 word1 和 word2 相同所需的最小步数，
// 每步可以删除任意一个字符串中的一个字符。
//
// 思路：
// 最终相等的字符串是 word1 和 word2 的某个公共子序列。
// 为了使删除次数最少，应保留最长公共子序列（LCS）。
// 最小删除步数 = len(word1) + len(word2) - 2 * LCS(word1, word2)
//
// LCS 使用空间优化的一维 DP 求解。
// 时间复杂度：O(m*n)，空间复杂度：O(min(m, n))。

// MinDistance 计算使两个单词相同的最小删除步数。
func MinDistance(word1, word2 string) int {
	m, n := len(word1), len(word2)
	if m == 0 {
		return n
	}
	if n == 0 {
		return m
	}

	// 确保 word2 是较短的，以优化空间
	if m < n {
		word1, word2 = word2, word1
		m, n = n, m
	}

	dp := make([]int, n+1)

	for i := 1; i <= m; i++ {
		prev := 0
		for j := 1; j <= n; j++ {
			temp := dp[j]
			if word1[i-1] == word2[j-1] {
				dp[j] = prev + 1
			} else {
				if dp[j] < dp[j-1] {
					dp[j] = dp[j-1]
				}
			}
			prev = temp
		}
	}

	lcs := dp[n]
	return m + n - 2*lcs
}
