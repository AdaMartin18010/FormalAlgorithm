package leetcode

import "testing"

func TestLengthOfLongestSubstring(t *testing.T) {
	tests := []struct {
		s        string
		expected int
	}{
		{"abcabcbb", 3},
		{"bbbbb", 1},
		{"pwwkew", 3},
		{"", 0},
		{"a", 1},
		{"abcdef", 6},
		{"abba", 2},
	}

	for _, tt := range tests {
		result := LengthOfLongestSubstring(tt.s)
		if result != tt.expected {
			t.Errorf("LengthOfLongestSubstring(%q) = %d, want %d", tt.s, result, tt.expected)
		}
	}
}
