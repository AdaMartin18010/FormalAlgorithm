package leetcode

import "testing"

func TestMinDistance(t *testing.T) {
	tests := []struct {
		name  string
		word1 string
		word2 string
		want  int
	}{
		{"Example 1", "horse", "ros", 3},
		{"Example 2", "intention", "execution", 5},
		{"Both empty", "", "", 0},
		{"Delete all", "abc", "", 3},
		{"Insert all", "", "abc", 3},
		{"Identical", "abc", "abc", 0},
		{"Kitten sitting", "kitten", "sitting", 3},
		{"Single replace", "a", "b", 1},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := MinDistance(tt.word1, tt.word2); got != tt.want {
				t.Errorf("MinDistance(%q, %q) = %d, want %d", tt.word1, tt.word2, got, tt.want)
			}
		})
	}
}
