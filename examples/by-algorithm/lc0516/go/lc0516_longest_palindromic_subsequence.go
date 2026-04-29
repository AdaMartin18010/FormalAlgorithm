package leetcode

// LeetCode 516. 最长回文子序列
//
// 给定一个字符串 s，找出其中最长的回文子序列，并返回该序列的长度。
//
// 思路：区间动态规划
// dp[i][j] = s[i..j] 的最长回文子序列长度。
// 若 s[i] == s[j]，则 dp[i][j] = dp[i+1][j-1] + 2。
// 若 s[i] != s[j]，则 dp[i][j] = max(dp[i+1][j], dp[i][j-1])。
// 边界：dp[i][i] = 1。
//
// 时间复杂度：O(n^2)，空间复杂度：O(n^2)。

// LongestPalindromeSubseq 计算字符串 s 的最长回文子序列长度。
func LongestPalindromeSubseq(s string) int {
	n := len(s)
	if n <= 1 {
		return n
	}

	// dp[i][j] = s[i..j] 的最长回文子序列长度
	dp := make([][]int, n)
	for i := range dp {
		dp[i] = make([]int, n)
		dp[i][i] = 1
	}

	// 按区间长度从小到大枚举
	for length := 2; length <= n; length++ {
		for i := 0; i <= n-length; i++ {
			j := i + length - 1
			if s[i] == s[j] {
				if length == 2 {
					dp[i][j] = 2
				} else {
					dp[i][j] = dp[i+1][j-1] + 2
				}
			} else {
				dp[i][j] = max(dp[i+1][j], dp[i][j-1])
			}
		}
	}

	return dp[0][n-1]
}
