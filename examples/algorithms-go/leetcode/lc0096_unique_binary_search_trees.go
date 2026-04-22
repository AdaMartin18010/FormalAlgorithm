package leetcode

// LeetCode 96 - Unique Binary Search Trees
// https://leetcode.com/problems/unique-binary-search-trees/
//
// Problem: Given an integer n, return the number of structurally unique BST's
// which has exactly n nodes of unique values from 1 to n.
//
// Approach: Catalan number DP. For each possible root value i (1..n),
// left subtree has i-1 nodes and right subtree has n-i nodes.
// dp[n] = Σ dp[i-1] * dp[n-i] for i = 1..n.
//
// Time: O(n²), Space: O(n).

// NumTrees returns the number of structurally unique BSTs with n nodes.
func NumTrees(n int) int {
	dp := make([]int, n+1)
	dp[0] = 1 // empty tree

	for nodes := 1; nodes <= n; nodes++ {
		for root := 1; root <= nodes; root++ {
			dp[nodes] += dp[root-1] * dp[nodes-root]
		}
	}

	return dp[n]
}
