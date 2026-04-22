package leetcode

import (
	"reflect"
	"testing"
)

func TestRotate(t *testing.T) {
	// 示例 1
	matrix1 := [][]int{
		{1, 2, 3},
		{4, 5, 6},
		{7, 8, 9},
	}
	Rotate(matrix1)
	expected1 := [][]int{
		{7, 4, 1},
		{8, 5, 2},
		{9, 6, 3},
	}
	if !reflect.DeepEqual(matrix1, expected1) {
		t.Errorf("Rotate example 1 failed: got %v, want %v", matrix1, expected1)
	}

	// 示例 2
	matrix2 := [][]int{
		{5, 1, 9, 11},
		{2, 4, 8, 10},
		{13, 3, 6, 7},
		{15, 14, 12, 16},
	}
	Rotate(matrix2)
	expected2 := [][]int{
		{15, 13, 2, 5},
		{14, 3, 4, 1},
		{12, 6, 8, 9},
		{16, 7, 10, 11},
	}
	if !reflect.DeepEqual(matrix2, expected2) {
		t.Errorf("Rotate example 2 failed: got %v, want %v", matrix2, expected2)
	}

	// 边界：单元素
	matrix3 := [][]int{{42}}
	Rotate(matrix3)
	if !reflect.DeepEqual(matrix3, [][]int{{42}}) {
		t.Errorf("Rotate single element failed: got %v", matrix3)
	}

	// 边界：2x2
	matrix4 := [][]int{
		{1, 2},
		{3, 4},
	}
	Rotate(matrix4)
	expected4 := [][]int{
		{3, 1},
		{4, 2},
	}
	if !reflect.DeepEqual(matrix4, expected4) {
		t.Errorf("Rotate 2x2 failed: got %v, want %v", matrix4, expected4)
	}
}
