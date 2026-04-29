package leetcode

import "testing"

func TestLongestPalindrome(t *testing.T) {
	tests := []struct {
		s        string
		expected string
	}{
		{"babad", "bab"}, // or "aba"
		{"cbbd", "bb"},
		{"a", "a"},
		{"aaaa", "aaaa"},
		{"abc", "a"},
		{"forgeeksskeegfor", "geeksskeeg"},
	}

	for _, tt := range tests {
		result := LongestPalindrome(tt.s)
		if result != tt.expected {
			// Special case: "babad" has two valid answers
			if tt.s == "babad" && result == "aba" {
				continue
			}
			if tt.s == "abc" && (result == "b" || result == "c") {
				continue
			}
			t.Errorf("LongestPalindrome(%q) = %q, want %q", tt.s, result, tt.expected)
		}
	}
}
