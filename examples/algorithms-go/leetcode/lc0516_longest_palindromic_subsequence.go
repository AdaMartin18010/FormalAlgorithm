package leetcode

// LeetCode 516. Longest Palindromic Subsequence
//
// Given a string s, find the longest palindromic subsequence's length in s.
//
// Approach 1: LCS duality — LPS(s) = LCS(s, reverse(s)).
// Approach 2 (implemented here): Interval DP.
// dp[i][j] = length of LPS in s[i:j+1].
//
// Time: O(n^2), Space: O(n^2)

func longestPalindromeSubseq(s string) int {
	n := len(s)
	if n <= 1 {
		return n
	}

	// dp[i][j] = LPS length for s[i..j]
	dp := make([][]int, n)
	for i := range dp {
		dp[i] = make([]int, n)
		dp[i][i] = 1 // single character is a palindrome of length 1
	}

	// Fill by increasing interval length
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

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
