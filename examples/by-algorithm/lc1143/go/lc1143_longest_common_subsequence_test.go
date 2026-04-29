package leetcode

import "testing"

func TestLongestCommonSubsequence(t *testing.T) {
	tests := []struct {
		text1    string
		text2    string
		expected int
	}{
		{"abcde", "ace", 3},
		{"abc", "abc", 3},
		{"abc", "def", 0},
		{"", "abc", 0},
		{"bsbininm", "jmjkbkjkv", 1},
	}

	for _, tt := range tests {
		result := LongestCommonSubsequence(tt.text1, tt.text2)
		if result != tt.expected {
			t.Errorf("LongestCommonSubsequence(%q, %q) = %d, want %d", tt.text1, tt.text2, result, tt.expected)
		}
	}
}
