package leetcode

import "testing"

func TestCountSubstrings(t *testing.T) {
	tests := []struct {
		name string
		s    string
		want int
	}{
		{"Example 1", "abc", 3},
		{"Example 2", "aaa", 6},
		{"Empty", "", 0},
		{"Single char", "a", 1},
		{"Two same", "aa", 3},
		{"Two diff", "ab", 2},
		{"Even palindrome", "abba", 6},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := CountSubstrings(tt.s); got != tt.want {
				t.Errorf("CountSubstrings(%q) = %d, want %d", tt.s, got, tt.want)
			}
		})
	}
}
