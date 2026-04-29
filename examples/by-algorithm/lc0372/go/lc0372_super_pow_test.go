package leetcode

import "testing"

func TestSuperPow(t *testing.T) {
	tests := []struct {
		a        int
		b        []int
		expected int
	}{
		{2, []int{3}, 8},
		{2, []int{1, 0}, 1024},
		{1, []int{4, 3, 3, 8, 5, 2}, 1},
		{2147483647, []int{2, 0, 0}, 1198},
		{2, []int{0}, 1},
	}

	for _, tt := range tests {
		result := SuperPow(tt.a, tt.b)
		if result != tt.expected {
			t.Errorf("SuperPow(%d, %v) = %d, want %d", tt.a, tt.b, result, tt.expected)
		}
	}
}
