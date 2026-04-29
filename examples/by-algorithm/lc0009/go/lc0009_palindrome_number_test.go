package leetcode

import "testing"

func TestIsPalindrome(t *testing.T) {
	tests := []struct {
		x        int
		expected bool
	}{
		{121, true},
		{-121, false},
		{10, false},
		{0, true},
		{5, true},
		{1221, true},
		{1234, false},
		{123454321, true},
		{2147483647, false},
	}

	for _, tt := range tests {
		result := IsPalindrome(tt.x)
		if result != tt.expected {
			t.Errorf("IsPalindrome(%d) = %v, want %v", tt.x, result, tt.expected)
		}
	}
}
