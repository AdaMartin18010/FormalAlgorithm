package algorithms

import "math"

// Knapsack01 solves the 0/1 knapsack problem.
// Returns the maximum value achievable with the given capacity.
// Time complexity: O(n * W). Space complexity: O(W).
func Knapsack01(weights, values []int, capacity int) int {
	n := len(weights)
	if n == 0 || capacity <= 0 {
		return 0
	}
	dp := make([]int, capacity+1)
	for i := 0; i < n; i++ {
		w := weights[i]
		v := values[i]
		for c := capacity; c >= w; c-- {
			if dp[c-w]+v > dp[c] {
				dp[c] = dp[c-w] + v
			}
		}
	}
	return dp[capacity]
}

// Knapsack01WithSelection solves 0/1 knapsack and returns (maxValue, selectedIndices).
func Knapsack01WithSelection(weights, values []int, capacity int) (int, []int) {
	n := len(weights)
	if n == 0 || capacity <= 0 {
		return 0, []int{}
	}
	// dp[i][c] = max value using first i items with capacity c
	dp := make([][]int, n+1)
	for i := range dp {
		dp[i] = make([]int, capacity+1)
	}
	for i := 1; i <= n; i++ {
		w := weights[i-1]
		v := values[i-1]
		for c := 0; c <= capacity; c++ {
			dp[i][c] = dp[i-1][c]
			if c >= w && dp[i-1][c-w]+v > dp[i][c] {
				dp[i][c] = dp[i-1][c-w] + v
			}
		}
	}
	// Backtrack to find selected items
	selected := []int{}
	c := capacity
	for i := n; i > 0 && c > 0; i-- {
		if dp[i][c] != dp[i-1][c] {
			selected = append(selected, i-1)
			c -= weights[i-1]
		}
	}
	// Reverse to maintain original order
	for i, j := 0, len(selected)-1; i < j; i, j = i+1, j-1 {
		selected[i], selected[j] = selected[j], selected[i]
	}
	return dp[n][capacity], selected
}

// LISLength returns the length of the longest increasing subsequence.
// Time complexity: O(n log n). Space complexity: O(n).
func LISLength(arr []int) int {
	if len(arr) == 0 {
		return 0
	}
	// tails[i] = smallest tail of all increasing subsequences of length i+1
	tails := []int{}
	for _, x := range arr {
		// Binary search for the first element >= x
		left, right := 0, len(tails)
		for left < right {
			mid := (left + right) / 2
			if tails[mid] < x {
				left = mid + 1
			} else {
				right = mid
			}
		}
		if left == len(tails) {
			tails = append(tails, x)
		} else {
			tails[left] = x
		}
	}
	return len(tails)
}

// LISDP returns the actual longest increasing subsequence.
// Time complexity: O(n²). Space complexity: O(n).
func LISDP(arr []int) []int {
	n := len(arr)
	if n == 0 {
		return []int{}
	}
	dp := make([]int, n)
	prev := make([]int, n)
	for i := range dp {
		dp[i] = 1
		prev[i] = -1
	}
	maxLen, maxIdx := 1, 0
	for i := 1; i < n; i++ {
		for j := 0; j < i; j++ {
			if arr[j] < arr[i] && dp[j]+1 > dp[i] {
				dp[i] = dp[j] + 1
				prev[i] = j
			}
		}
		if dp[i] > maxLen {
			maxLen = dp[i]
			maxIdx = i
		}
	}
	// Reconstruct
	result := make([]int, 0, maxLen)
	for i := maxIdx; i >= 0; i = prev[i] {
		result = append(result, arr[i])
		if prev[i] == -1 {
			break
		}
	}
	// Reverse
	for i, j := 0, len(result)-1; i < j; i, j = i+1, j-1 {
		result[i], result[j] = result[j], result[i]
	}
	return result
}

// CoinChangeMin returns the minimum number of coins to make amount.
// Returns -1 if impossible.
func CoinChangeMin(coins []int, amount int) int {
	if amount == 0 {
		return 0
	}
	dp := make([]int, amount+1)
	for i := 1; i <= amount; i++ {
		dp[i] = math.MaxInt32
	}
	for i := 1; i <= amount; i++ {
		for _, coin := range coins {
			if coin > 0 && coin <= i && dp[i-coin] != math.MaxInt32 {
				if dp[i-coin]+1 < dp[i] {
					dp[i] = dp[i-coin] + 1
				}
			}
		}
	}
	if dp[amount] == math.MaxInt32 {
		return -1
	}
	return dp[amount]
}

// CoinChangeWays returns the number of ways to make amount using the given coins.
func CoinChangeWays(coins []int, amount int) int {
	dp := make([]int, amount+1)
	dp[0] = 1
	for _, coin := range coins {
		for i := coin; i <= amount; i++ {
			dp[i] += dp[i-coin]
		}
	}
	return dp[amount]
}
