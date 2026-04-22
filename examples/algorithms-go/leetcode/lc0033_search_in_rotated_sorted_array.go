// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
package leetcode

// SearchRotated 在旋转排序数组中搜索目标值的索引。
//
// 形式化规约：
//   Pre: nums 为某个升序无重复数组经一次旋转所得，len(nums) >= 0。
//   Post: 若 target 在 nums 中，返回索引 i 满足 nums[i] == target；否则返回 -1。
//
// 循环不变式：
//   设当前搜索区间为 [left, right]（闭区间）。
//   若 target 存在于 nums，则其索引必然位于 [left, right] 之内。
//
//   维护：
//   - 旋转数组的性质：至少有一半是有序的。
//   - 取 mid = left + (right-left)/2：
//     * 若 nums[left] <= nums[mid]，左半部分有序：
//       - 若 target 落在 [nums[left], nums[mid]) 内，right = mid - 1。
//       - 否则 left = mid + 1。
//     * 若 nums[left] > nums[mid]，右半部分有序：
//       - 若 target 落在 (nums[mid], nums[right]] 内，left = mid + 1。
//       - 否则 right = mid - 1。
//   - 新区间仍包含可能的目标索引。
//
//   终止推出：当 left > right 时区间为空，由不变式知 target 不在数组中，返回 -1。
//
// 复杂度：
//   时间复杂度: O(log n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 正确性依赖于「旋转排序数组中至少有一半是有序的」这一性质。
//   - 详细证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
//   - 终止性由区间长度严格递减保证。
func SearchRotated(nums []int, target int) int {
	if len(nums) == 0 {
		return -1
	}

	left, right := 0, len(nums)-1

	for left <= right {
		mid := left + (right-left)/2
		midVal := nums[mid]

		if midVal == target {
			return mid
		}

		leftVal := nums[left]

		if leftVal <= midVal {
			// 左半部分有序
			if target >= leftVal && target < midVal {
				right = mid - 1
			} else {
				left = mid + 1
			}
		} else {
			// 右半部分有序
			rightVal := nums[right]
			if target > midVal && target <= rightVal {
				left = mid + 1
			} else {
				right = mid - 1
			}
		}
	}

	return -1
}
