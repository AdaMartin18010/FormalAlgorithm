package leetcode

import (
	"math"
	"testing"
)

func TestMyPow(t *testing.T) {
	tests := []struct {
		x        float64
		n        int
		expected float64
		eps      float64
	}{
		{2.0, 10, 1024.0, 1e-9},
		{2.1, 3, 9.261, 1e-3},
		{2.0, -2, 0.25, 1e-9},
		{0.0, 0, 1.0, 1e-9},
		{99.0, 0, 1.0, 1e-9},
		{-2.0, 3, -8.0, 1e-9},
	}

	for _, tt := range tests {
		result := MyPow(tt.x, tt.n)
		if math.Abs(result-tt.expected) > tt.eps {
			t.Errorf("MyPow(%v, %d) = %v, want %v", tt.x, tt.n, result, tt.expected)
		}
	}

	// Min int should not overflow/inf
	result := MyPow(2.0, math.MinInt32)
	if math.IsInf(result, 0) {
		t.Errorf("MyPow(2.0, MinInt32) should be finite")
	}
}
