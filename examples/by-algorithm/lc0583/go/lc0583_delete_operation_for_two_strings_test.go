package leetcode

import "testing"

func TestMinDistance583(t *testing.T) {
	tests := []struct {
		word1    string
		word2    string
		expected int
	}{
		{"sea", "eat", 2},
		{"leetcode", "etco", 4},
		{"", "abc", 3},
		{"abc", "abc", 0},
		{"abc", "def", 6},
	}

	for _, tt := range tests {
		result := MinDistance583(tt.word1, tt.word2)
		if result != tt.expected {
			t.Errorf("MinDistance583(%q, %q) = %d, want %d", tt.word1, tt.word2, result, tt.expected)
		}
	}
}
