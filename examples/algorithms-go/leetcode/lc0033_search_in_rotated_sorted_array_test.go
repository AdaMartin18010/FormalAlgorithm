package leetcode

import "testing"

func TestSearchRotated(t *testing.T) {
	tests := []struct {
		nums     []int
		target   int
		expected int
	}{
		// LeetCode 官方示例
		{[]int{4, 5, 6, 7, 0, 1, 2}, 0, 4},
		{[]int{4, 5, 6, 7, 0, 1, 2}, 3, -1},
		{[]int{1}, 0, -1},
		// 边界条件
		{[]int{}, 1, -1},
		{[]int{5}, 5, 0},
		{[]int{5}, 1, -1},
		{[]int{1, 2, 3, 4, 5}, 3, 2},
		{[]int{1, 2, 3, 4, 5}, 6, -1},
		{[]int{3, 4, 5, 1, 2}, 1, 3},
	}

	for _, tt := range tests {
		result := SearchRotated(tt.nums, tt.target)
		if result != tt.expected {
			t.Errorf("SearchRotated(%v, %d) = %d, want %d", tt.nums, tt.target, result, tt.expected)
		}
	}
}

func TestSearchRotatedLargeArray(t *testing.T) {
	nums := make([]int, 10_000)
	for i := 0; i < 5_000; i++ {
		nums[i] = 5_000 + i
	}
	for i := 0; i < 5_000; i++ {
		nums[5_000+i] = i
	}

	if result := SearchRotated(nums, 7_500); result != 2_500 {
		t.Errorf("SearchRotated large array target found = %d, want 2500", result)
	}
	if result := SearchRotated(nums, 10_001); result != -1 {
		t.Errorf("SearchRotated large array target not found = %d, want -1", result)
	}
}
