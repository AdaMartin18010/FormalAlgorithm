package leetcode

import "testing"

func TestFindMin(t *testing.T) {
	tests := []struct {
		nums     []int
		expected int
	}{
		// LeetCode 官方示例
		{[]int{3, 4, 5, 1, 2}, 1},
		{[]int{4, 5, 6, 7, 0, 1, 2}, 0},
		{[]int{11, 13, 15, 17}, 11},
		// 边界条件
		{[]int{5}, 5},
		{[]int{2, 1}, 1},
		{[]int{1, 2}, 1},
		{[]int{1, 2, 3, 4, 5}, 1},
		{[]int{2, 3, 4, 5, 1}, 1},
	}

	for _, tt := range tests {
		result := FindMin(tt.nums)
		if result != tt.expected {
			t.Errorf("FindMin(%v) = %d, want %d", tt.nums, result, tt.expected)
		}
	}
}

func TestFindMinLargeArray(t *testing.T) {
	nums := make([]int, 10_000)
	for i := 0; i < 5_000; i++ {
		nums[i] = 5_000 + i
	}
	for i := 0; i < 5_000; i++ {
		nums[5_000+i] = i
	}

	if result := FindMin(nums); result != 0 {
		t.Errorf("FindMin large array = %d, want 0", result)
	}
}
