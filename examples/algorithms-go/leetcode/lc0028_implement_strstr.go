// LeetCode 28. Implement strStr()
// https://leetcode.com/problems/implement-strstr/
//
// Problem: Return the index of the first occurrence of needle in haystack,
// or -1 if needle is not part of haystack. Return 0 when needle is empty.
//
// Formal specification:
// - Pre: haystack length n, needle length m
// - Post: min { i | 0 ≤ i ≤ n-m, haystack[i:i+m] == needle } or -1
//
// Algorithm: KMP (Knuth-Morris-Pratt). Compute prefix function pi for needle,
// then linear scan through haystack with O(n+m) time.
//
// Time: O(n + m), Space: O(m).

package leetcode

// StrStr returns the first index of needle in haystack, or -1.
func StrStr(haystack, needle string) int {
	if len(needle) == 0 {
		return 0
	}
	n, m := len(haystack), len(needle)
	if n < m {
		return -1
	}

	// Compute prefix function pi
	pi := make([]int, m)
	k := 0
	for q := 1; q < m; q++ {
		for k > 0 && needle[k] != needle[q] {
			k = pi[k-1]
		}
		if needle[k] == needle[q] {
			k++
		}
		pi[q] = k
	}

	// KMP matching
	q := 0
	for i := 0; i < n; i++ {
		for q > 0 && needle[q] != haystack[i] {
			q = pi[q-1]
		}
		if needle[q] == haystack[i] {
			q++
		}
		if q == m {
			return i + 1 - m
		}
	}

	return -1
}
