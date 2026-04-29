package leetcode

// LeetCode 416. 分割等和子集 / Partition Equal Subset Sum
//
// 给你一个只包含正整数的非空数组 nums 。请你判断是否可以将这个数组分割成两个子集，
// 使得两个子集的元素和相等。
//
// 题目链接: https://leetcode.com/problems/partition-equal-subset-sum/
// 难度: Medium
//
// 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.5
//
// ## 问题转化（0/1 背包判定）
//
// 设 total = sum(nums)。若 total 为奇数，直接返回 false。
// 否则目标为：能否从 nums 中选出一个子集，使其和为 target = total / 2？
//
// ## 状态转移方程（布尔型 DP）
//
// dp[w] = dp[w] OR dp[w - nums[i]]  (逆序遍历，0/1 背包)

// CanPartition 判断数组是否能被分割成两个和相等的子集。
//
// 时间复杂度: O(n * target) — target = sum(nums) / 2
// 空间复杂度: O(target) — 一维布尔数组
func CanPartition(nums []int) bool {
	total := 0
	for _, num := range nums {
		total += num
	}
	if total%2 != 0 {
		return false
	}

	target := total / 2
	dp := make([]bool, target+1)
	dp[0] = true

	for _, num := range nums {
		// 逆序遍历：0/1 背包核心技巧，确保每个数字只用一次
		for w := target; w >= num; w-- {
			dp[w] = dp[w] || dp[w-num]
		}
		// 提前终止
		if dp[target] {
			return true
		}
	}

	return dp[target]
}
