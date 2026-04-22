package leetcode

import "testing"

func TestNumTrees(t *testing.T) {
	tests := []struct {
		name string
		n    int
		want int
	}{
		{"Example 1", 3, 5},
		{"Example 2", 1, 1},
		{"Zero nodes", 0, 1},
		{"Catalan 2", 2, 2},
		{"Catalan 4", 4, 14},
		{"Catalan 5", 5, 42},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := NumTrees(tt.n); got != tt.want {
				t.Errorf("NumTrees(%d) = %d, want %d", tt.n, got, tt.want)
			}
		})
	}
}
