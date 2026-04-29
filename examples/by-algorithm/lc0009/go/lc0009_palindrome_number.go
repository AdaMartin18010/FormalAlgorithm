// LeetCode 9. Palindrome Number
// https://leetcode.com/problems/palindrome-number/
//
// Problem: Given an integer x, return true if x is a palindrome, and false otherwise.
//
// Formal specification:
// - Pre: x ∈ Z
// - Post: return true iff decimal representation of x reads the same forward and backward
//
// Algorithm: Reverse half of the number. Avoids overflow from reversing the entire number.
//
// Time: O(log₁₀ n), Space: O(1).

package leetcode

// IsPalindrome returns true if x is a palindrome integer.
func IsPalindrome(x int) bool {
	if x < 0 {
		return false
	}
	if x < 10 {
		return true
	}
	if x%10 == 0 {
		return false
	}

	reversed := 0
	for x > reversed {
		reversed = reversed*10 + x%10
		x /= 10
	}

	// Even-length: x == reversed
	// Odd-length: x == reversed/10 (middle digit ignored)
	return x == reversed || x == reversed/10
}
