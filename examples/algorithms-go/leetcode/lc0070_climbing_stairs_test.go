package leetcode

import "testing"

func TestClimbStairs(t *testing.T) {
	tests := []struct {
		name string
		n    int
		want int
	}{
		{"Example 1", 2, 2},
		{"Example 2", 3, 3},
		{"Single step", 1, 1},
		{"Four steps", 4, 5},
		{"Fibonacci check", 10, 89},
		{"Max constraint", 45, 1836311903},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := ClimbStairs(tt.n); got != tt.want {
				t.Errorf("ClimbStairs(%d) = %d, want %d", tt.n, got, tt.want)
			}
		})
	}
}
