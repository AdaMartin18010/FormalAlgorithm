// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
package leetcode

// Search 在有序数组中查找目标值的索引。
//
// 形式化规约：
//   Pre: nums 为升序排列，len(nums) >= 0，元素互不相同（或按题意可重复）。
//   Post: 若 target 在 nums 中，返回索引 i 满足 nums[i] == target；否则返回 -1。
//
// 循环不变式：
//   设当前搜索区间为 [left, right]（闭区间）。
//   若 target 存在于 nums，则其索引必然位于 [left, right] 之内。
//
//   维护：
//   - 初始 left = 0，right = n-1，不变式显然成立。
//   - 取 mid = left + (right-left)/2：
//     * 若 nums[mid] == target，已找到，返回 mid。
//     * 若 nums[mid] < target，目标若在数组中必在右半区，left = mid + 1。
//     * 若 nums[mid] > target，目标若在数组中必在左半区，right = mid - 1。
//   - 新区间仍包含可能的目标索引。
//
//   终止推出：当 left > right 时区间为空，由不变式知 target 不在数组中，返回 -1。
//
// 复杂度：
//   时间复杂度: O(log n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
//   - 终止性由区间长度严格递减保证。
func Search(nums []int, target int) int {
	left, right := 0, len(nums)-1

	for left <= right {
		mid := left + (right-left)/2
		midVal := nums[mid]

		if midVal == target {
			return mid
		}

		if midVal < target {
			left = mid + 1
		} else {
			right = mid - 1
		}
	}

	return -1
}
