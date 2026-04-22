package leetcode

import "testing"

func TestLengthOfLIS(t *testing.T) {
	tests := []struct {
		name string
		nums []int
		want int
	}{
		{"Example 1", []int{10, 9, 2, 5, 3, 7, 101, 18}, 4},
		{"Example 2", []int{0, 1, 0, 3, 2, 3}, 4},
		{"Example 3", []int{7, 7, 7, 7, 7, 7, 7}, 1},
		{"Single", []int{1}, 1},
		{"Decreasing", []int{5, 4, 3, 2, 1}, 1},
		{"Increasing", []int{1, 2, 3, 4, 5}, 5},
	}

	for _, tt := range tests {
		t.Run(tt.name+"_DP", func(t *testing.T) {
			if got := LengthOfLISDP(tt.nums); got != tt.want {
				t.Errorf("LengthOfLISDP(%v) = %d, want %d", tt.nums, got, tt.want)
			}
		})
		t.Run(tt.name+"_Binary", func(t *testing.T) {
			if got := LengthOfLISBinary(tt.nums); got != tt.want {
				t.Errorf("LengthOfLISBinary(%v) = %d, want %d", tt.nums, got, tt.want)
			}
		})
	}
}

func TestLengthOfLISEquivalence(t *testing.T) {
	testCases := [][]int{
		{10, 9, 2, 5, 3, 7, 101, 18},
		{0, 1, 0, 3, 2, 3},
		{7, 7, 7, 7, 7},
		{1, 3, 6, 7, 9, 4, 10, 5, 6},
		{3, 1, 2, 1, 8, 5, 6},
	}

	for _, nums := range testCases {
		dpResult := LengthOfLISDP(append([]int(nil), nums...))
		binaryResult := LengthOfLISBinary(append([]int(nil), nums...))
		if dpResult != binaryResult {
			t.Errorf("Mismatch for %v: dp=%d, binary=%d", nums, dpResult, binaryResult)
		}
	}
}
