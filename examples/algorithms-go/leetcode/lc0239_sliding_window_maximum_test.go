package leetcode

import (
	"reflect"
	"testing"
)

func TestMaxSlidingWindow(t *testing.T) {
	tests := []struct {
		nums     []int
		k        int
		expected []int
	}{
		{[]int{1, 3, -1, -3, 5, 3, 6, 7}, 3, []int{3, 3, 5, 5, 6, 7}},
		{[]int{1}, 1, []int{1}},
		{[]int{1, 2, 3, 4}, 4, []int{4}},
		{[]int{1, 2, 3, 4, 5}, 2, []int{2, 3, 4, 5}},
		{[]int{5, 4, 3, 2, 1}, 2, []int{5, 4, 3, 2}},
		{[]int{5, 5, 5, 5}, 2, []int{5, 5, 5}},
		{[]int{-1, -3, -5, -2}, 2, []int{-1, -3, -2}},
	}

	for _, tt := range tests {
		result := MaxSlidingWindow(tt.nums, tt.k)
		if !reflect.DeepEqual(result, tt.expected) {
			t.Errorf("MaxSlidingWindow(%v, %d) = %v, want %v", tt.nums, tt.k, result, tt.expected)
		}
	}
}
