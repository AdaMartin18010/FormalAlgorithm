// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
package leetcode

// Jump 计算到达最后一个位置的最小跳跃次数。
//
// 形式化规约：
//   Pre: nums 为非负整数数组，len(nums) >= 1，保证可以到达最后一个位置。
//   Post: 返回从索引 0 到达索引 n-1 的最小跳跃次数。
//
// 核心思路：
//   贪心法（BFS 思想）：维护当前层的最远边界 currentEnd 和下一层的最远边界 farthest。
//   当遍历到 currentEnd 时，必须再进行一次跳跃，将 currentEnd 更新为 farthest。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
func Jump(nums []int) int {
	n := len(nums)
	if n <= 1 {
		return 0
	}

	jumps := 0
	currentEnd := 0
	farthest := 0

	for i := 0; i < n-1; i++ {
		if i+nums[i] > farthest {
			farthest = i + nums[i]
		}
		if i == currentEnd {
			jumps++
			currentEnd = farthest
			if currentEnd >= n-1 {
				break
			}
		}
	}

	return jumps
}
