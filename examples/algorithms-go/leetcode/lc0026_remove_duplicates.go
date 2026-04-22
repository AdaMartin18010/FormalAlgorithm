// LeetCode 26. Remove Duplicates from Sorted Array
// https://leetcode.com/problems/remove-duplicates-from-sorted-array/
//
// Problem: Given a sorted array nums, remove the duplicates in-place such that
// each element appears only once and returns the new length.
//
// Formal specification:
// - Pre: nums is sorted in non-decreasing order
// - Post: return k where nums[0:k] contains each distinct element once, in original order
//
// Algorithm: Two pointers (slow/fast). Slow points to next write position.
// Time: O(n), Space: O(1).
//
// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/01-双指针.md

package leetcode

// RemoveDuplicates 原地删除有序数组中的重复项，返回去重后的长度。
// 使用双指针：slow 指向已去重区域的下一个写入位置，fast 遍历数组。
func RemoveDuplicates(nums []int) int {
	n := len(nums)
	if n == 0 {
		return 0
	}

	slow := 1
	for fast := 1; fast < n; fast++ {
		if nums[fast] != nums[slow-1] {
			nums[slow] = nums[fast]
			slow++
		}
	}
	return slow
}
