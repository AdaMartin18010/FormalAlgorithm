package leetcode

// LeetCode 647 - Palindromic Substrings
// https://leetcode.com/problems/palindromic-substrings/
//
// Problem: Given a string s, return the number of palindromic substrings in it.
//
// Approach: Center expansion. For each center (2n-1 centers),
// expand outward while characters match. Count each valid expansion.
//
// Time: O(n²), Space: O(1).

// CountSubstrings returns the number of palindromic substrings.
func CountSubstrings(s string) int {
	n := len(s)
	if n == 0 {
		return 0
	}

	count := 0
	for center := 0; center < 2*n-1; center++ {
		left := center / 2
		right := left + center%2

		for left >= 0 && right < n && s[left] == s[right] {
			count++
			left--
			right++
		}
	}

	return count
}
