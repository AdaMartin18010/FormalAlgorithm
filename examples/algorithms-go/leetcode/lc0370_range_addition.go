// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
package leetcode

// GetModifiedArray 应用所有区间更新后返回最终数组。
//
// 形式化规约：
//   Pre: length >= 1；updates 中每个元素满足 0 <= start <= end < length。
//   Post: 返回应用所有更新后的数组。
//
// 核心思路：
//   差分数组惰性更新。对区间 [l, r] 加 inc：diff[l] += inc，diff[r+1] -= inc。
//   最后对 diff 求前缀和还原。
//
// 复杂度：
//   时间复杂度: O(n + m)
//   空间复杂度: O(n)
func GetModifiedArray(length int, updates [][]int) []int {
	diff := make([]int, length)

	for _, update := range updates {
		start, end, inc := update[0], update[1], update[2]
		diff[start] += inc
		if end+1 < length {
			diff[end+1] -= inc
		}
	}

	result := make([]int, length)
	result[0] = diff[0]
	for i := 1; i < length; i++ {
		result[i] = result[i-1] + diff[i]
	}

	return result
}
