package leetcode

// LeetCode 198. 打家劫舍 / House Robber
//
// 你是一个专业的小偷，计划偷窃沿街的房屋。每间房内都藏有一定的现金，
// 影响你偷窃的唯一制约因素就是相邻的房屋装有相互连通的防盗系统，
// 如果两间相邻的房屋在同一晚上被小偷闯入，系统会自动报警。
//
// 给定一个代表每个房屋存放金额的非负整数数组，计算你今晚在不触动警报装置的情况下，
// 能够偷窃到的最高金额。
//
// 题目链接: https://leetcode.com/problems/house-robber/
// 难度: Medium
//
// 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.2
//
// ## 状态转移方程
//
// dp[i] = max(dp[i-1], dp[i-2] + nums[i])
//
// ## 最优子结构引理
//
// 引理: 前 i 间房屋的最优解要么不偷第 i 间 (=OPT(i-1))，
//   要么偷第 i 间 (=OPT(i-2) + nums[i])。两种情况取最大值。

// Rob 计算在不触发警报的情况下能偷窃到的最高金额。
//
// 时间复杂度: O(n) — 单次遍历
// 空间复杂度: O(1) — 滚动变量
func Rob(nums []int) int {
	n := len(nums)
	if n == 0 {
		return 0
	}
	if n == 1 {
		return nums[0]
	}

	prev2 := nums[0]
	prev1 := max(nums[0], nums[1])

	for i := 2; i < n; i++ {
		curr := max(prev1, prev2+nums[i])
		prev2 = prev1
		prev1 = curr
	}

	return prev1
}
