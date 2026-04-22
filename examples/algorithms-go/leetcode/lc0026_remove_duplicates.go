// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// RemoveDuplicates 原地删除有序数组中的重复元素，返回新长度。
//
// 形式化规约：
//   Pre: nums 为按非降序排列的整数数组，长度 ∈ [0, 3*10^4]。
//   Post: 返回 k，nums 的前 k 个元素为去重后的结果，每个值恰好出现一次。
//
// 循环不变式：
//   每次迭代开始时，nums[0..slow-1] 为已处理的去重结果，无重复元素，
//   且恰好是 nums[0..fast-1] 中所有不同元素按原顺序的排列。
//
//   维护：
//   - nums[fast] == nums[slow-1]：仅 fast++。
//   - nums[fast] != nums[slow-1]：nums[slow] = nums[fast]，两者均++。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
//   - 关键：排序保证相同元素连续出现，只需比较相邻元素。
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
