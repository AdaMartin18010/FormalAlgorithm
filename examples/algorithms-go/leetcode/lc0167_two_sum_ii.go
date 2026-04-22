// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// TwoSumII 在已排序数组中找到和为目标值的两个数的索引（1-based）。
//
// 形式化规约：
//   Pre: numbers 为按非降序排列的整数数组，长度 ∈ [2, 3*10^4]。
//        题目保证恰好存在一个有效答案。
//   Post: 返回 [i, j]，满足 numbers[i-1]+numbers[j-1] == target 且 i < j。
//
// 循环不变式：
//   设当前指针为 l, r。若解存在，则解的两个索引必在 [l, r] 范围内。
//
//   维护：
//   - sum == target：找到解，返回。
//   - sum < target：numbers[l] 太小，任何 k < r 的配对 (l,k) 都有
//     numbers[l]+numbers[k] ≤ numbers[l]+numbers[r] < target，故 l++。
//   - sum > target：numbers[r] 太大，任何 k > l 的配对 (k,r) 都有
//     numbers[k]+numbers[r] ≥ numbers[l]+numbers[r] > target，故 r--。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 不遗漏解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
func TwoSumII(numbers []int, target int) []int {
	left, right := 0, len(numbers)-1

	for left < right {
		sum := numbers[left] + numbers[right]
		if sum == target {
			return []int{left + 1, right + 1}
		} else if sum < target {
			left++
		} else {
			right--
		}
	}

	return []int{-1, -1}
}
