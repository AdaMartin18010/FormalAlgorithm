package leetcode

import (
	"reflect"
	"testing"
)

func TestThreeSum(t *testing.T) {
	// 示例 1
	result1 := ThreeSum([]int{-1, 0, 1, 2, -1, -4})
	expected1 := [][]int{{-1, -1, 2}, {-1, 0, 1}}
	if !reflect.DeepEqual(result1, expected1) {
		t.Errorf("ThreeSum example 1 = %v, want %v", result1, expected1)
	}

	// 示例 2
	result2 := ThreeSum([]int{0, 1, 1})
	if len(result2) != 0 {
		t.Errorf("ThreeSum example 2 = %v, want empty", result2)
	}

	// 示例 3
	result3 := ThreeSum([]int{0, 0, 0})
	expected3 := [][]int{{0, 0, 0}}
	if !reflect.DeepEqual(result3, expected3) {
		t.Errorf("ThreeSum example 3 = %v, want %v", result3, expected3)
	}

	// 边界：空数组
	if len(ThreeSum([]int{})) != 0 {
		t.Error("Expected empty for empty array")
	}

	// 边界：不足三个元素
	if len(ThreeSum([]int{1, 2})) != 0 {
		t.Error("Expected empty for less than 3 elements")
	}

	// 边界：全正数
	if len(ThreeSum([]int{1, 2, 3})) != 0 {
		t.Error("Expected empty for all positive")
	}

	// 边界：大量重复
	resultDup := ThreeSum([]int{0, 0, 0, 0, 0})
	expectedDup := [][]int{{0, 0, 0}}
	if !reflect.DeepEqual(resultDup, expectedDup) {
		t.Errorf("ThreeSum duplicates = %v, want %v", resultDup, expectedDup)
	}
}
