package leetcode

import "testing"

func TestMinSubArrayLen(t *testing.T) {
	tests := []struct {
		target   int
		nums     []int
		expected int
	}{
		{7, []int{2, 3, 1, 2, 4, 3}, 2},
		{4, []int{1, 4, 4}, 1},
		{11, []int{1, 1, 1, 1, 1, 1, 1, 1}, 0},
		{5, []int{5}, 1},
		{5, []int{3}, 0},
		{10, []int{1, 2, 3, 4}, 4},
		{15, []int{1, 2, 3, 10, 5}, 1},
	}

	for _, tt := range tests {
		result := MinSubArrayLen(tt.target, tt.nums)
		if result != tt.expected {
			t.Errorf("MinSubArrayLen(%d, %v) = %d, want %d", tt.target, tt.nums, result, tt.expected)
		}
	}
}

func TestMinSubArrayLenLarge(t *testing.T) {
	large := make([]int, 100000)
	for i := range large {
		large[i] = 1
	}
	if MinSubArrayLen(100000, large) != 100000 {
		t.Error("Large array exact failed")
	}
	if MinSubArrayLen(50000, large) != 50000 {
		t.Error("Large array half failed")
	}
}
