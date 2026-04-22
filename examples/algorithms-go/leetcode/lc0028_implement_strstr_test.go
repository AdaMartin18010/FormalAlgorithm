package leetcode

import "testing"

func TestStrStr(t *testing.T) {
	tests := []struct {
		haystack string
		needle   string
		expected int
	}{
		{"hello", "ll", 2},
		{"aaaaa", "bba", -1},
		{"", "", 0},
		{"hello", "", 0},
		{"", "a", -1},
		{"aaaa", "aa", 0},
		{"abcabcabc", "abc", 0},
		{"abcdef", "gh", -1},
		{"abc", "abcd", -1},
		{"a", "a", 0},
		{"abc", "c", 2},
	}

	for _, tt := range tests {
		result := StrStr(tt.haystack, tt.needle)
		if result != tt.expected {
			t.Errorf("StrStr(%q, %q) = %d, want %d", tt.haystack, tt.needle, result, tt.expected)
		}
	}
}
