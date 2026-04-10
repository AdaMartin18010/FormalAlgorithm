// dp.go - 动态规划经典问题实现
// 包含0/1背包问题、完全背包、最长递增子序列(LIS)、最长公共子序列(LCS)

package main

import (
	"fmt"
	"math"
)

// ==================== 0/1 背包问题 ====================

// Knapsack01 0/1背包问题
// weights: 物品重量数组
// values: 物品价值数组
// capacity: 背包容量
// 返回最大价值和选择的物品
func Knapsack01(weights, values []int, capacity int) (int, []int) {
	n := len(weights)
	// dp[i][j] 表示前i个物品，容量为j时的最大价值
	dp := make([][]int, n+1)
	for i := range dp {
		dp[i] = make([]int, capacity+1)
	}
	
	// 填充DP表
	for i := 1; i <= n; i++ {
		for j := 0; j <= capacity; j++ {
			// 不选第i个物品
			dp[i][j] = dp[i-1][j]
			// 选第i个物品（如果可以放下）
			if j >= weights[i-1] {
				value := dp[i-1][j-weights[i-1]] + values[i-1]
				if value > dp[i][j] {
					dp[i][j] = value
				}
			}
		}
	}
	
	// 回溯找出选择的物品
	selected := []int{}
	w := capacity
	for i := n; i > 0; i-- {
		if dp[i][w] != dp[i-1][w] {
			selected = append([]int{i-1}, selected...)
			w -= weights[i-1]
		}
	}
	
	return dp[n][capacity], selected
}

// Knapsack01Optimized 0/1背包空间优化版
func Knapsack01Optimized(weights, values []int, capacity int) int {
	n := len(weights)
	dp := make([]int, capacity+1)
	
	for i := 0; i < n; i++ {
		// 倒序遍历，避免重复计算
		for j := capacity; j >= weights[i]; j-- {
			value := dp[j-weights[i]] + values[i]
			if value > dp[j] {
				dp[j] = value
			}
		}
	}
	
	return dp[capacity]
}

// ==================== 完全背包问题 ====================

// UnboundedKnapsack 完全背包问题（每种物品可以选无限次）
func UnboundedKnapsack(weights, values []int, capacity int) int {
	n := len(weights)
	dp := make([]int, capacity+1)
	
	for i := 0; i < n; i++ {
		// 正序遍历，可以重复选择
		for j := weights[i]; j <= capacity; j++ {
			value := dp[j-weights[i]] + values[i]
			if value > dp[j] {
				dp[j] = value
			}
		}
	}
	
	return dp[capacity]
}

// CoinChange 硬币兑换问题（最少硬币数）
// coins: 硬币面额
// amount: 目标金额
// 返回最少硬币数，如果无解返回-1
func CoinChange(coins []int, amount int) int {
	dp := make([]int, amount+1)
	for i := 1; i <= amount; i++ {
		dp[i] = math.MaxInt32
	}
	
	for _, coin := range coins {
		for j := coin; j <= amount; j++ {
			if dp[j-coin]+1 < dp[j] {
				dp[j] = dp[j-coin] + 1
			}
		}
	}
	
	if dp[amount] == math.MaxInt32 {
		return -1
	}
	return dp[amount]
}

// CoinChangeWays 硬币兑换方案数
func CoinChangeWays(coins []int, amount int) int {
	dp := make([]int, amount+1)
	dp[0] = 1
	
	for _, coin := range coins {
		for j := coin; j <= amount; j++ {
			dp[j] += dp[j-coin]
		}
	}
	
	return dp[amount]
}

// ==================== 最长递增子序列 (LIS) ====================

// LIS 最长递增子序列 - O(n^2) 动态规划解法
func LIS(nums []int) (int, []int) {
	n := len(nums)
	if n == 0 {
		return 0, nil
	}
	
	// dp[i] 表示以nums[i]结尾的最长递增子序列长度
	dp := make([]int, n)
	parent := make([]int, n) // 用于重建路径
	
	for i := 0; i < n; i++ {
		dp[i] = 1
		parent[i] = -1
		for j := 0; j < i; j++ {
			if nums[j] < nums[i] && dp[j]+1 > dp[i] {
				dp[i] = dp[j] + 1
				parent[i] = j
			}
		}
	}
	
	// 找到最大值及其位置
	maxLen, maxIdx := 0, 0
	for i := 0; i < n; i++ {
		if dp[i] > maxLen {
			maxLen = dp[i]
			maxIdx = i
		}
	}
	
	// 重建子序列
	seq := []int{}
	for i := maxIdx; i != -1; i = parent[i] {
		seq = append([]int{nums[i]}, seq...)
	}
	
	return maxLen, seq
}

// LISBinarySearch 最长递增子序列 - O(n log n) 二分查找解法
func LISBinarySearch(nums []int) int {
	n := len(nums)
	if n == 0 {
		return 0
	}
	
	// tails[i] 表示长度为i+1的递增子序列的最小末尾元素
	tails := make([]int, 0, n)
	
	for _, num := range nums {
		// 二分查找插入位置
		left, right := 0, len(tails)
		for left < right {
			mid := (left + right) / 2
			if tails[mid] < num {
				left = mid + 1
			} else {
				right = mid
			}
		}
		
		if left == len(tails) {
			tails = append(tails, num)
		} else {
			tails[left] = num
		}
	}
	
	return len(tails)
}

// ==================== 最长公共子序列 (LCS) ====================

// LCS 最长公共子序列
func LCS(s1, s2 string) (int, string) {
	m, n := len(s1), len(s2)
	
	// dp[i][j] 表示s1[0:i]和s2[0:j]的LCS长度
	dp := make([][]int, m+1)
	for i := range dp {
		dp[i] = make([]int, n+1)
	}
	
	// 填充DP表
	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if s1[i-1] == s2[j-1] {
				dp[i][j] = dp[i-1][j-1] + 1
			} else {
				if dp[i-1][j] > dp[i][j-1] {
					dp[i][j] = dp[i-1][j]
				} else {
					dp[i][j] = dp[i][j-1]
				}
			}
		}
	}
	
	// 回溯重建LCS
	lcs := []byte{}
	i, j := m, n
	for i > 0 && j > 0 {
		if s1[i-1] == s2[j-1] {
			lcs = append([]byte{s1[i-1]}, lcs...)
			i--
			j--
		} else if dp[i-1][j] > dp[i][j-1] {
			i--
		} else {
			j--
		}
	}
	
	return dp[m][n], string(lcs)
}

// LCSAll 求所有最长公共子序列（可能有多个）
func LCSAll(s1, s2 string) []string {
	m, n := len(s1), len(s2)
	dp := make([][]int, m+1)
	for i := range dp {
		dp[i] = make([]int, n+1)
	}
	
	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if s1[i-1] == s2[j-1] {
				dp[i][j] = dp[i-1][j-1] + 1
			} else if dp[i-1][j] > dp[i][j-1] {
				dp[i][j] = dp[i-1][j]
			} else if dp[i-1][j] < dp[i][j-1] {
				dp[i][j] = dp[i][j-1]
			} else {
				dp[i][j] = dp[i-1][j]
			}
		}
	}
	
	result := make(map[string]bool)
	var backtrack func(int, int, []byte)
	backtrack = func(i, j int, current []byte) {
		if i == 0 || j == 0 {
			if len(current) > 0 {
				result[string(current)] = true
			}
			return
		}
		
		if s1[i-1] == s2[j-1] {
			backtrack(i-1, j-1, append([]byte{s1[i-1]}, current...))
		} else {
			if dp[i-1][j] >= dp[i][j-1] {
				backtrack(i-1, j, current)
			}
			if dp[i][j-1] >= dp[i-1][j] {
				backtrack(i, j-1, current)
			}
		}
	}
	
	backtrack(m, n, []byte{})
	
	lcsList := make([]string, 0, len(result))
	for s := range result {
		lcsList = append(lcsList, s)
	}
	return lcsList
}

// ==================== 其他经典DP问题 ====================

// EditDistance 编辑距离（Levenshtein距离）
func EditDistance(s1, s2 string) int {
	m, n := len(s1), len(s2)
	dp := make([][]int, m+1)
	for i := range dp {
		dp[i] = make([]int, n+1)
	}
	
	// 初始化边界
	for i := 0; i <= m; i++ {
		dp[i][0] = i
	}
	for j := 0; j <= n; j++ {
		dp[0][j] = j
	}
	
	// 填充DP表
	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if s1[i-1] == s2[j-1] {
				dp[i][j] = dp[i-1][j-1]
			} else {
				insert := dp[i][j-1] + 1
				delete := dp[i-1][j] + 1
				replace := dp[i-1][j-1] + 1
				dp[i][j] = min(insert, min(delete, replace))
			}
		}
	}
	
	return dp[m][n]
}

// MaxSubarray 最大子数组和（Kadane算法）
func MaxSubarray(nums []int) (int, int, int) {
	n := len(nums)
	if n == 0 {
		return 0, -1, -1
	}
	
	maxSum := nums[0]
	currSum := nums[0]
	start, end := 0, 0
	tempStart := 0
	
	for i := 1; i < n; i++ {
		if currSum+nums[i] < nums[i] {
			currSum = nums[i]
			tempStart = i
		} else {
			currSum += nums[i]
		}
		
		if currSum > maxSum {
			maxSum = currSum
			start = tempStart
			end = i
		}
	}
	
	return maxSum, start, end
}

// MatrixChain 矩阵链乘法最优括号化
func MatrixChain(dimensions []int) (int, [][]int) {
	n := len(dimensions) - 1
	// dp[i][j] 表示计算矩阵i到j的最小乘法次数
	dp := make([][]int, n)
	split := make([][]int, n)
	
	for i := range dp {
		dp[i] = make([]int, n)
		split[i] = make([]int, n)
	}
	
	// 链长度从2开始
	for length := 2; length <= n; length++ {
		for i := 0; i <= n-length; i++ {
			j := i + length - 1
			dp[i][j] = math.MaxInt32
			for k := i; k < j; k++ {
				cost := dp[i][k] + dp[k+1][j] + dimensions[i]*dimensions[k+1]*dimensions[j+1]
				if cost < dp[i][j] {
					dp[i][j] = cost
					split[i][j] = k
				}
			}
		}
	}
	
	return dp[0][n-1], split
}

// 辅助函数
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// ==================== 测试示例 ====================

func main() {
	fmt.Println("=================== 动态规划算法测试 ===================")
	
	// 测试1: 0/1背包
	fmt.Println("\n1. 0/1背包问题:")
	weights := []int{2, 3, 4, 5}
	values := []int{3, 4, 5, 6}
	capacity := 8
	maxValue, selected := Knapsack01(weights, values, capacity)
	fmt.Printf("  物品重量: %v\n", weights)
	fmt.Printf("  物品价值: %v\n", values)
	fmt.Printf("  背包容量: %d\n", capacity)
	fmt.Printf("  最大价值: %d\n", maxValue)
	fmt.Printf("  选择的物品索引: %v\n", selected)
	
	optValue := Knapsack01Optimized(weights, values, capacity)
	fmt.Printf("  空间优化版结果: %d\n", optValue)
	
	// 测试2: 完全背包
	fmt.Println("\n2. 完全背包问题:")
	weights2 := []int{1, 3, 4}
	values2 := []int{15, 20, 30}
	capacity2 := 10
	maxValue2 := UnboundedKnapsack(weights2, values2, capacity2)
	fmt.Printf("  最大价值: %d\n", maxValue2)
	
	// 测试3: 硬币兑换
	fmt.Println("\n3. 硬币兑换问题:")
	coins := []int{1, 2, 5}
	amount := 11
	minCoins := CoinChange(coins, amount)
	ways := CoinChangeWays(coins, amount)
	fmt.Printf("  硬币面额: %v\n", coins)
	fmt.Printf("  目标金额: %d\n", amount)
	fmt.Printf("  最少硬币数: %d\n", minCoins)
	fmt.Printf("  兑换方案数: %d\n", ways)
	
	// 测试4: LIS
	fmt.Println("\n4. 最长递增子序列 (LIS):")
	nums := []int{10, 9, 2, 5, 3, 7, 101, 18}
	length, sequence := LIS(nums)
	fmt.Printf("  数组: %v\n", nums)
	fmt.Printf("  LIS长度: %d\n", length)
	fmt.Printf("  LIS序列: %v\n", sequence)
	
	length2 := LISBinarySearch(nums)
	fmt.Printf("  二分查找法LIS长度: %d\n", length2)
	
	// 测试5: LCS
	fmt.Println("\n5. 最长公共子序列 (LCS):")
	s1, s2 := "ABCDGH", "AEDFHR"
	lcsLen, lcs := LCS(s1, s2)
	fmt.Printf("  字符串1: %s\n", s1)
	fmt.Printf("  字符串2: %s\n", s2)
	fmt.Printf("  LCS长度: %d\n", lcsLen)
	fmt.Printf("  LCS: %s\n", lcs)
	
	// 测试多LCS
	s3, s4 := "ABC", "ACB"
	allLCS := LCSAll(s3, s4)
	fmt.Printf("  \n字符串1: %s, 字符串2: %s\n", s3, s4)
	fmt.Printf("  所有LCS: %v\n", allLCS)
	
	// 测试6: 编辑距离
	fmt.Println("\n6. 编辑距离:")
	word1, word2 := "horse", "ros"
	distance := EditDistance(word1, word2)
	fmt.Printf("  '%s' -> '%s' 的编辑距离: %d\n", word1, word2, distance)
	
	// 测试7: 最大子数组
	fmt.Println("\n7. 最大子数组和:")
	nums2 := []int{-2, 1, -3, 4, -1, 2, 1, -5, 4}
	maxSum, start, end := MaxSubarray(nums2)
	fmt.Printf("  数组: %v\n", nums2)
	fmt.Printf("  最大子数组和: %d\n", maxSum)
	fmt.Printf("  子数组范围: [%d, %d]\n", start, end)
	fmt.Printf("  子数组: %v\n", nums2[start:end+1])
	
	// 测试8: 矩阵链乘法
	fmt.Println("\n8. 矩阵链乘法:")
	dims := []int{10, 30, 5, 60}
	minOps, _ := MatrixChain(dims)
	fmt.Printf("  矩阵维度: %v\n", dims)
	fmt.Printf("  最小乘法次数: %d\n", minOps)
	
	fmt.Println("\n=================== 测试完成 ===================")
}
