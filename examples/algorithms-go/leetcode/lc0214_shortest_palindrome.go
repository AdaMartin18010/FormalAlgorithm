package leetcode

// LeetCode 214 - Shortest Palindrome
// https://leetcode.com/problems/shortest-palindrome/
//
// Problem: Given a string s, convert it to a palindrome by adding characters in front.
// Return the shortest palindrome you can find.
//
// Approach: KMP prefix function. Concatenate s + "#" + reverse(s),
// compute the prefix function. The last value gives the length of the
// longest palindromic prefix of s. Prepend the reverse of the remaining suffix.
//
// Time: O(n), Space: O(n).

// ShortestPalindrome returns the shortest palindrome by prepending characters.
func ShortestPalindrome(s string) string {
	n := len(s)
	if n == 0 {
		return s
	}

	// Build reverse(s)
	rev := make([]byte, n)
	for i := 0; i < n; i++ {
		rev[i] = s[n-1-i]
	}

	// Build combined: s + "#" + rev
	combined := make([]byte, 0, 2*n+1)
	combined = append(combined, s...)
	combined = append(combined, '#')
	combined = append(combined, rev...)
	m := len(combined)

	// KMP prefix function
	pi := make([]int, m)
	for i := 1; i < m; i++ {
		j := pi[i-1]
		for j > 0 && combined[i] != combined[j] {
			j = pi[j-1]
		}
		if combined[i] == combined[j] {
			j++
		}
		pi[i] = j
	}

	prefixLen := pi[m-1]
	return string(rev[:n-prefixLen]) + s
}
