package leetcode

import "testing"

func TestMaxCoins(t *testing.T) {
	tests := []struct {
		name string
		nums []int
		want int
	}{
		{"Example 1", []int{3, 1, 5, 8}, 167},
		{"Example 2", []int{1, 5}, 10},
		{"Single", []int{5}, 5},
		{"Two", []int{3, 1}, 6},
		{"All ones", []int{1, 1, 1, 1}, 4},
		{"Zeros", []int{0, 0}, 0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := MaxCoins(tt.nums); got != tt.want {
				t.Errorf("MaxCoins(%v) = %d, want %d", tt.nums, got, tt.want)
			}
		})
	}
}
