package leetcode

import "testing"

func TestMaxArea(t *testing.T) {
	tests := []struct {
		height   []int
		expected int
	}{
		{[]int{1, 8, 6, 2, 5, 4, 8, 3, 7}, 49},
		{[]int{1, 1}, 1},
		{[]int{1, 2, 3, 4, 5}, 6},
		{[]int{5, 4, 3, 2, 1}, 6},
		{[]int{5, 5, 5, 5}, 15},
		{[]int{0, 2, 0}, 0},
	}

	for _, tt := range tests {
		result := MaxArea(tt.height)
		if result != tt.expected {
			t.Errorf("MaxArea(%v) = %d, want %d", tt.height, result, tt.expected)
		}
	}
}

func TestMaxAreaLarge(t *testing.T) {
	large := make([]int, 10000)
	for i := range large {
		large[i] = i + 1
	}
	if MaxArea(large) != 25000000 {
		t.Errorf("MaxArea large array = %d, want 25000000", MaxArea(large))
	}
}
