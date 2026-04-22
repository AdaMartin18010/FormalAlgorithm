package leetcode

// LeetCode 583. Delete Operation for Two Strings
//
// Given two strings word1 and word2, return the minimum number of steps
// required to make word1 and word2 the same.
//
// In one step, you can delete exactly one character in either string.
//
// Key insight: The minimum deletions = (len(word1) - LCS) + (len(word2) - LCS)
//                                          = len(word1) + len(word2) - 2*LCS
//
// We compute LCS using space-optimized DP.
//
// Time: O(m*n), Space: O(min(m,n))

func minDistanceDel(word1 string, word2 string) int {
	m, n := len(word1), len(word2)
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
