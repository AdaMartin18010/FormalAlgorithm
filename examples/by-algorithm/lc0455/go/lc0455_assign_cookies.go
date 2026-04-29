// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
package leetcode

import "sort"

// FindContentChildren 计算最多能满足的孩子数量。
//
// 形式化规约：
//   Pre: g 为孩子胃口值数组，s 为饼干尺寸数组。
//   Post: 返回能满足的孩子的最大数量。
//
// 核心思路：
//   贪心策略：排序后双指针，用最小满足饼干满足每个孩子。
//
// 复杂度：
//   时间复杂度: O(m log m + n log n)
//   空间复杂度: O(1)
func FindContentChildren(g []int, s []int) int {
	sort.Ints(g)
	sort.Ints(s)

	child, cookie := 0, 0
	for child < len(g) && cookie < len(s) {
		if s[cookie] >= g[child] {
			child++
		}
		cookie++
	}

	return child
}
