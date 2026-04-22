package leetcode

import "testing"

func TestMinWindow(t *testing.T) {
	tests := []struct {
		s        string
		t        string
		expected string
	}{
		{"ADOBECODEBANC", "ABC", "BANC"},
		{"a", "a", "a"},
		{"a", "aa", ""},
		{"abc", "abc", "abc"},
		{"abcdef", "abc", "abc"},
		{"xyzabc", "abc", "abc"},
		{"Aa", "a", "a"},
		{"aaabbbccc", "abc", "abbbc"},
	}

	for _, tt := range tests {
		result := MinWindow(tt.s, tt.t)
		if result != tt.expected {
			t.Errorf("MinWindow(%q, %q) = %q, want %q", tt.s, tt.t, result, tt.expected)
		}
	}
}
