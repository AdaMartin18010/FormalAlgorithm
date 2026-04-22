// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
package leetcode

import "sort"

// EraseOverlapIntervals 计算需要移除的最小区间数量，使剩余区间互不重叠。
//
// 形式化规约：
//   Pre: intervals 为区间集合，每个元素为 [start, end]。
//   Post: 返回需要移除的最小区间数量。
//
// 核心思路：
//   贪心策略：按结束时间排序，每次选择结束最早的且与已选区间不重叠的区间。
//
// 复杂度：
//   时间复杂度: O(n log n)
//   空间复杂度: O(1)
func EraseOverlapIntervals(intervals [][]int) int {
	n := len(intervals)
	if n == 0 {
		return 0
	}

	sort.Slice(intervals, func(i, j int) bool {
		return intervals[i][1] < intervals[j][1]
	})

	count := 1
	end := intervals[0][1]

	for i := 1; i < n; i++ {
		if intervals[i][0] >= end {
			count++
			end = intervals[i][1]
		}
	}

	return n - count
}
