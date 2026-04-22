package leetcode

// LeetCode 312. 戳气球 / Burst Balloons
//
// 有 n 个气球，编号为 0 到 n-1，每个气球上都标有一个数字，这些数字存在数组 nums 中。
//
// 现在要求你戳破所有的气球。戳破第 i 个气球，你可以获得 nums[left] * nums[i] * nums[right] 个硬币。
// 这里的 left 和 right 表示和 i 相邻的两个气球的序号。
//
// 题目链接: https://leetcode.com/problems/burst-balloons/
// 难度: Hard
//
// 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.6
//
// ## 状态转移方程（区间 DP）
//
// 在数组两端添加虚拟气球 1：val = [1] + nums + [1]
// dp[i][j] = max_{i < k < j} { dp[i][k] + dp[k][j] + val[i] * val[k] * val[j] }
//
// 其中 dp[i][j] 表示开区间 (i, j) 内所有气球戳破能获得的最大硬币数。

// MaxCoins 计算戳破所有气球能获得的最大硬币数。
//
// 时间复杂度: O(n^3) — 区间长度 × 区间起点 × 分割点
// 空间复杂度: O(n^2) — 二维 DP 表
func MaxCoins(nums []int) int {
	n := len(nums)
	// 扩展数组，两端添加虚拟气球 1
	val := make([]int, n+2)
	val[0] = 1
	for i := 0; i < n; i++ {
		val[i+1] = nums[i]
	}
	val[n+1] = 1

	// dp[i][j] = 开区间 (i, j) 能获得的最大硬币
	dp := make([][]int, n+2)
	for i := range dp {
		dp[i] = make([]int, n+2)
	}

	// 按区间长度从小到大填表
	for length := 2; length <= n+1; length++ {
		for i := 0; i <= n+1-length; i++ {
			j := i + length
			for k := i + 1; k < j; k++ {
				candidate := dp[i][k] + dp[k][j] + val[i]*val[k]*val[j]
				if candidate > dp[i][j] {
					dp[i][j] = candidate
				}
			}
		}
	}

	return dp[0][n+1]
}
