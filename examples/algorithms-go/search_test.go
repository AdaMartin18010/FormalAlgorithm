package algorithms

import "testing"

func TestBinarySearch(t *testing.T) {
	arr := []int{1, 3, 5, 7, 9}
	tests := []struct {
		target   int
		expected int
	}{
		{5, 2},
		{1, 0},
		{9, 4},
		{0, -1},
		{10, -1},
		{4, -1},
	}
	for _, tt := range tests {
		result := BinarySearch(arr, tt.target)
		if result != tt.expected {
			t.Errorf("BinarySearch(%v, %d) = %d, want %d", arr, tt.target, result, tt.expected)
		}
	}
}

func TestBinarySearchEmpty(t *testing.T) {
	if BinarySearch([]int{}, 1) != -1 {
		t.Error("BinarySearch on empty slice should return -1")
	}
}

func TestLowerBound(t *testing.T) {
	arr := []int{1, 3, 5, 5, 7, 9}
	tests := []struct {
		target   int
		expected int
	}{
		{5, 2},
		{4, 2},
		{10, 6},
		{0, 0},
		{1, 0},
	}
	for _, tt := range tests {
		result := LowerBound(arr, tt.target)
		if result != tt.expected {
			t.Errorf("LowerBound(%v, %d) = %d, want %d", arr, tt.target, result, tt.expected)
		}
	}
}

func TestUpperBound(t *testing.T) {
	arr := []int{1, 3, 5, 5, 7, 9}
	tests := []struct {
		target   int
		expected int
	}{
		{5, 4},
		{4, 2},
		{10, 6},
		{0, 0},
		{9, 6},
	}
	for _, tt := range tests {
		result := UpperBound(arr, tt.target)
		if result != tt.expected {
			t.Errorf("UpperBound(%v, %d) = %d, want %d", arr, tt.target, result, tt.expected)
		}
	}
}
