package leetcode

import "testing"

func TestShortestPalindrome(t *testing.T) {
	tests := []struct {
		name string
		s    string
		want string
	}{
		{"Example 1", "aacecaaa", "aaacecaaa"},
		{"Example 2", "abcd", "dcbabcd"},
		{"Empty", "", ""},
		{"Single char", "a", "a"},
		{"Already palindrome", "aba", "aba"},
		{"Even palindrome", "aa", "aa"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := ShortestPalindrome(tt.s); got != tt.want {
				t.Errorf("ShortestPalindrome(%q) = %q, want %q", tt.s, got, tt.want)
			}
		})
	}
}
