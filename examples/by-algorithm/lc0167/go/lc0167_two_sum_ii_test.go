package leetcode

import (
	"reflect"
	"testing"
)

func TestTwoSumII(t *testing.T) {
	tests := []struct {
		numbers  []int
		target   int
		expected []int
	}{
		{[]int{2, 7, 11, 15}, 9, []int{1, 2}},
		{[]int{2, 3, 4}, 6, []int{1, 3}},
		{[]int{-1, 0}, -1, []int{1, 2}},
		{[]int{1, 2}, 3, []int{1, 2}},
		{[]int{-5, -3, -1, 0, 2}, -8, []int{1, 2}},
		{[]int{0, 0, 3, 4}, 0, []int{1, 2}},
	}

	for _, tt := range tests {
		result := TwoSumII(tt.numbers, tt.target)
		if !reflect.DeepEqual(result, tt.expected) {
			t.Errorf("TwoSumII(%v, %d) = %v, want %v", tt.numbers, tt.target, result, tt.expected)
		}
	}
}

func TestTwoSumIILarge(t *testing.T) {
	large := make([]int, 10000)
	for i := range large {
		large[i] = i + 1
	}
	result := TwoSumII(large, 19999)
	expected := []int{9999, 10000}
	if !reflect.DeepEqual(result, expected) {
		t.Errorf("TwoSumII large = %v, want %v", result, expected)
	}
}
