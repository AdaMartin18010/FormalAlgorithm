package algorithms

import (
	"reflect"
	"testing"
)

func TestQuickSort(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		expected []int
	}{
		{"empty", []int{}, []int{}},
		{"single", []int{5}, []int{5}},
		{"sorted", []int{1, 2, 3, 4, 5}, []int{1, 2, 3, 4, 5}},
		{"reverse", []int{5, 4, 3, 2, 1}, []int{1, 2, 3, 4, 5}},
		{"random", []int{3, 6, 8, 10, 1, 2, 1}, []int{1, 1, 2, 3, 6, 8, 10}},
		{"duplicates", []int{2, 2, 2, 1, 1}, []int{1, 1, 2, 2, 2}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			arr := make([]int, len(tt.input))
			copy(arr, tt.input)
			QuickSort(arr)
			if !reflect.DeepEqual(arr, tt.expected) {
				t.Errorf("QuickSort(%v) = %v, want %v", tt.input, arr, tt.expected)
			}
		})
	}
}

func TestMergeSort(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		expected []int
	}{
		{"empty", []int{}, []int{}},
		{"single", []int{5}, []int{5}},
		{"sorted", []int{1, 2, 3}, []int{1, 2, 3}},
		{"reverse", []int{3, 2, 1}, []int{1, 2, 3}},
		{"random", []int{38, 27, 43, 3, 9, 82, 10}, []int{3, 9, 10, 27, 38, 43, 82}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := MergeSort(tt.input)
			if !reflect.DeepEqual(result, tt.expected) {
				t.Errorf("MergeSort(%v) = %v, want %v", tt.input, result, tt.expected)
			}
		})
	}
}

func TestHeapSort(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		expected []int
	}{
		{"empty", []int{}, []int{}},
		{"single", []int{5}, []int{5}},
		{"sorted", []int{1, 2, 3, 4}, []int{1, 2, 3, 4}},
		{"reverse", []int{4, 3, 2, 1}, []int{1, 2, 3, 4}},
		{"random", []int{12, 11, 13, 5, 6, 7}, []int{5, 6, 7, 11, 12, 13}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			arr := make([]int, len(tt.input))
			copy(arr, tt.input)
			HeapSort(arr)
			if !reflect.DeepEqual(arr, tt.expected) {
				t.Errorf("HeapSort(%v) = %v, want %v", tt.input, arr, tt.expected)
			}
		})
	}
}

func TestInsertionSort(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		expected []int
	}{
		{"empty", []int{}, []int{}},
		{"single", []int{5}, []int{5}},
		{"sorted", []int{1, 2, 3}, []int{1, 2, 3}},
		{"reverse", []int{3, 2, 1}, []int{1, 2, 3}},
		{"random", []int{64, 34, 25, 12, 22, 11, 90}, []int{11, 12, 22, 25, 34, 64, 90}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			arr := make([]int, len(tt.input))
			copy(arr, tt.input)
			InsertionSort(arr)
			if !reflect.DeepEqual(arr, tt.expected) {
				t.Errorf("InsertionSort(%v) = %v, want %v", tt.input, arr, tt.expected)
			}
		})
	}
}

func TestCountingSort(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		maxVal   int
		expected []int
	}{
		{"empty", []int{}, 0, []int{}},
		{"basic", []int{4, 2, 2, 8, 3, 3, 1}, 8, []int{1, 2, 2, 3, 3, 4, 8}},
		{"sorted", []int{1, 2, 3, 4}, 4, []int{1, 2, 3, 4}},
		{"reverse", []int{4, 3, 2, 1}, 4, []int{1, 2, 3, 4}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := CountingSort(tt.input, tt.maxVal)
			if !reflect.DeepEqual(result, tt.expected) {
				t.Errorf("CountingSort(%v, %d) = %v, want %v", tt.input, tt.maxVal, result, tt.expected)
			}
		})
	}
}
