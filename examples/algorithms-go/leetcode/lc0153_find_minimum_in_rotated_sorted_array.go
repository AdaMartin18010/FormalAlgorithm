// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
package leetcode

// FindMin 寻找旋转排序数组中的最小值。
//
// 形式化规约：
//   Pre: nums 为某个升序无重复数组经若干次旋转所得，len(nums) >= 1。
//   Post: 返回 nums 中最小元素的值，即 min(nums)。
//
// 循环不变式：
//   设当前搜索区间为 [left, right]（闭区间）。
//   最小元素始终位于 [left, right] 范围内。
//
//   维护：
//   - 初始 left = 0，right = n-1，不变式显然成立。
//   - 取 mid = left + (right-left)/2：
//     * 若 nums[mid] > nums[right]，最小值在右半部分，left = mid + 1。
//     * 若 nums[mid] < nums[right]，[mid, right] 整体有序，最小值在左半部分或就是 mid，
//       right = mid。
//     * 因元素互不相同，不会出现 nums[mid] == nums[right]。
//   - 新区间仍包含最小值。
//
//   终止推出：当 left == right 时，区间仅含一个元素，由不变式知其即为最小值。
//
// 复杂度：
//   时间复杂度: O(log n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 关键性质：在旋转排序数组中，nums[mid] 与 nums[right] 的大小关系
//     唯一确定了最小值所在的半区。
//   - 详细证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
//   - 终止性由 left < right 条件及区间长度严格递减保证。
func FindMin(nums []int) int {
	left, right := 0, len(nums)-1

	for left < right {
		mid := left + (right-left)/2

		if nums[mid] > nums[right] {
			left = mid + 1
		} else {
			// nums[mid] < nums[right]，因元素互不相同
			right = mid
		}
	}

	return nums[left]
}
