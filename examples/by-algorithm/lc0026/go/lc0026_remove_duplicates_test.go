package leetcode

import (
	"reflect"
	"testing"
)

func TestRemoveDuplicates(t *testing.T) {
	// 示例 1
	nums1 := []int{1, 1, 2}
	k1 := RemoveDuplicates(nums1)
	if k1 != 2 || !reflect.DeepEqual(nums1[:k1], []int{1, 2}) {
		t.Errorf("RemoveDuplicates example 1: k=%d, nums=%v", k1, nums1[:k1])
	}

	// 示例 2
	nums2 := []int{0, 0, 1, 1, 1, 2, 2, 3, 3, 4}
	k2 := RemoveDuplicates(nums2)
	if k2 != 5 || !reflect.DeepEqual(nums2[:k2], []int{0, 1, 2, 3, 4}) {
		t.Errorf("RemoveDuplicates example 2: k=%d, nums=%v", k2, nums2[:k2])
	}

	// 边界：空数组
	if RemoveDuplicates([]int{}) != 0 {
		t.Error("Expected 0 for empty array")
	}

	// 边界：单元素
	numsSingle := []int{5}
	kSingle := RemoveDuplicates(numsSingle)
	if kSingle != 1 || !reflect.DeepEqual(numsSingle[:kSingle], []int{5}) {
		t.Errorf("Single element failed: k=%d", kSingle)
	}

	// 边界：全不同
	numsDistinct := []int{1, 2, 3, 4, 5}
	kDistinct := RemoveDuplicates(numsDistinct)
	if kDistinct != 5 || !reflect.DeepEqual(numsDistinct[:kDistinct], []int{1, 2, 3, 4, 5}) {
		t.Errorf("All distinct failed")
	}

	// 边界：全相同
	numsSame := []int{2, 2, 2, 2, 2}
	kSame := RemoveDuplicates(numsSame)
	if kSame != 1 || !reflect.DeepEqual(numsSame[:kSame], []int{2}) {
		t.Errorf("All same failed")
	}
}
