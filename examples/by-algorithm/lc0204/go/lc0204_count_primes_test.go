package leetcode

import "testing"

func TestCountPrimes(t *testing.T) {
	tests := []struct {
		name string
		n    int
		want int
	}{
		{"Example 1", 10, 4}, // 2,3,5,7
		{"Example 2", 0, 0},
		{"Example 3", 1, 0},
		{"n is prime", 7, 3}, // 2,3,5
		{"Large", 100, 25},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := CountPrimes(tt.n); got != tt.want {
				t.Errorf("CountPrimes(%d) = %d, want %d", tt.n, got, tt.want)
			}
		})
	}
}
