// LeetCode 5. Longest Palindromic Substring
// https://leetcode.com/problems/longest-palindromic-substring/
//
// Problem: Given a string s, return the longest palindromic substring in s.
//
// Formal specification:
// - Pre: s is a string of length n
// - Post: return substring s[l..r] such that s[l..r] == reverse(s[l..r]) and length is maximal
//
// Algorithm: Expand around center. Enumerate 2n-1 centers (character centers + gap centers),
// expand outward while palindrome holds, record the longest.
//
// Time: O(n^2), Space: O(1).

package leetcode

// LongestPalindrome returns the longest palindromic substring in s.
func LongestPalindrome(s string) string {
	n := len(s)
	if n == 0 {
		return ""
	}

	start, maxLen := 0, 1

	// expand returns the length of palindrome expanded from left, right.
	expand := func(left, right int) int {
		l, r := left, right
		for l >= 0 && r < n && s[l] == s[r] {
			l--
			r++
		}
		return r - l - 1
	}

	for i := 0; i < n; i++ {
		len1 := expand(i, i)   // odd length
		len2 := expand(i, i+1) // even length
		length := len1
		if len2 > length {
			length = len2
		}
		if length > maxLen {
			maxLen = length
			start = i - (length-1)/2
		}
	}

	return s[start : start+maxLen]
}
