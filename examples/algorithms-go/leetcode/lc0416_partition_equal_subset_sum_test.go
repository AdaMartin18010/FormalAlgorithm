package leetcode

import "testing"

func TestCanPartition(t *testing.T) {
	tests := []struct {
		name string
		nums []int
		want bool
	}{
		{"Example 1", []int{1, 5, 11, 5}, true},
		{"Example 2", []int{1, 2, 3, 5}, false},
		{"Single element", []int{1}, false},
		{"Two equal", []int{2, 2}, true},
		{"Odd sum", []int{1, 2, 4}, false},
		{"All ones", []int{1, 1, 1, 1, 1, 1, 1, 1}, true},
		{"Complex", []int{3, 3, 3, 4, 5}, true},
		{"Impossible", []int{100, 100, 100, 100, 100, 100, 100, 100, 1}, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := CanPartition(tt.nums); got != tt.want {
				t.Errorf("CanPartition(%v) = %v, want %v", tt.nums, got, tt.want)
			}
		})
	}
}
