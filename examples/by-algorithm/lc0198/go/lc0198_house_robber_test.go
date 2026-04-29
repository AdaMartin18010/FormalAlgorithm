package leetcode

import "testing"

func TestRob(t *testing.T) {
	tests := []struct {
		name string
		nums []int
		want int
	}{
		{"Example 1", []int{1, 2, 3, 1}, 4},
		{"Example 2", []int{2, 7, 9, 3, 1}, 12},
		{"Empty", []int{}, 0},
		{"Single", []int{5}, 5},
		{"Two", []int{2, 1}, 2},
		{"Alternating", []int{2, 1, 1, 2}, 4},
		{"All same", []int{5, 5, 5, 5, 5}, 15},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := Rob(tt.nums); got != tt.want {
				t.Errorf("Rob(%v) = %d, want %d", tt.nums, got, tt.want)
			}
		})
	}
}
