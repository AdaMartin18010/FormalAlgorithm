package leetcode

import "testing"

func TestSearch(t *testing.T) {
	tests := []struct {
		nums     []int
		target   int
		expected int
	}{
		// LeetCode 官方示例
		{[]int{-1, 0, 3, 5, 9, 12}, 9, 4},
		{[]int{-1, 0, 3, 5, 9, 12}, 2, -1},
		// 边界条件
		{[]int{}, 1, -1},
		{[]int{5}, 5, 0},
		{[]int{5}, 1, -1},
		{[]int{2, 2, 2, 2}, 2, 1},
		{[]int{2, 2, 2, 2}, 3, -1},
		{[]int{1, 2, 3, 4, 5}, 1, 0},
		{[]int{1, 2, 3, 4, 5}, 5, 4},
	}

	for _, tt := range tests {
		result := Search(tt.nums, tt.target)
		if result != tt.expected {
			t.Errorf("Search(%v, %d) = %d, want %d", tt.nums, tt.target, result, tt.expected)
		}
	}
}

func TestSearchLargeArray(t *testing.T) {
	nums := make([]int, 10_000)
	for i := range nums {
		nums[i] = i
	}

	if result := Search(nums, 5_000); result != 5_000 {
		t.Errorf("Search large array target found = %d, want 5000", result)
	}
	if result := Search(nums, 10_001); result != -1 {
		t.Errorf("Search large array target not found = %d, want -1", result)
	}
}
