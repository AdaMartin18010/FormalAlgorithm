package leetcode

// LeetCode 72. Edit Distance
//
// Given two strings word1 and word2, return the minimum number of operations
// required to convert word1 to word2.
//
// You have the following three operations permitted on a word:
// - Insert a character
// - Delete a character
// - Replace a character
//
// Approach: 2D DP with rolling array optimization.
// dp[i][j] = min distance between word1[0:i] and word2[0:j].
// We use two 1D arrays (prev and curr) to achieve O(min(m,n)) space.
//
// Time: O(m*n), Space: O(min(m,n))

func MinDistance(word1 string, word2 string) int {
	m, n := len(word1), len(word2)
	// Make word2 the shorter one for space optimization
	if n > m {
		word1, word2 = word2, word1
		m, n = n, m
	}

	// prev represents dp[i-1][*], curr represents dp[i][*]
	prev := make([]int, n+1)
	curr := make([]int, n+1)

	// Base case: converting empty word1 to word2[0:j] requires j insertions
	for j := 0; j <= n; j++ {
		prev[j] = j
	}

	for i := 1; i <= m; i++ {
		curr[0] = i // converting word1[0:i] to empty requires i deletions
		for j := 1; j <= n; j++ {
			if word1[i-1] == word2[j-1] {
				curr[j] = prev[j-1]
			} else {
				// delete: prev[j] + 1, insert: curr[j-1] + 1, replace: prev[j-1] + 1
				curr[j] = min(prev[j]+1, min(curr[j-1]+1, prev[j-1]+1))
			}
		}
		// Swap prev and curr for next iteration
		prev, curr = curr, prev
	}

	return prev[n]
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
