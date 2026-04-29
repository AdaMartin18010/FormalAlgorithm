package leetcode

import "testing"

func TestSearchMatrix(t *testing.T) {
	matrix := [][]int{
		{1, 4, 7, 11, 15},
		{2, 5, 8, 12, 19},
		{3, 6, 9, 16, 22},
		{10, 13, 14, 17, 24},
		{18, 21, 23, 26, 30},
	}
	tests := []struct {
		target int
		want   bool
	}{
		{5, true},
		{20, false},
		{1, true},
		{30, true},
		{0, false},
	}
	for _, tt := range tests {
		if got := SearchMatrix(matrix, tt.target); got != tt.want {
			t.Errorf("SearchMatrix(target=%d) = %v, want %v", tt.target, got, tt.want)
		}
	}
}
