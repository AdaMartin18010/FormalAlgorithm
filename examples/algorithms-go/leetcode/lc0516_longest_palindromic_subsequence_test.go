package leetcode

import "testing"

func TestLongestPalindromeSubseq(t *testing.T) {
	tests := []struct {
		input    string
		expected int
	}{
		{"bbbab", 4},
		{"cbbd", 2},
		{"a", 1},
		{"aaaa", 4},
		{"abc", 1},
	}

	for _, tt := range tests {
		result := LongestPalindromeSubseq(tt.input)
		if result != tt.expected {
			t.Errorf("LongestPalindromeSubseq(%q) = %d, want %d", tt.input, result, tt.expected)
		}
	}
}
