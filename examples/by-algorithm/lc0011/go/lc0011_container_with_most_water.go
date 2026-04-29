// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// MaxArea 计算能容纳最多水的容器面积。
//
// 形式化规约：
//   Pre: height 为长度 n ∈ [2, 10^5] 的非负整数数组，height[i] ∈ [0, 10^4]。
//   Post: 返回 max_{0 ≤ i < j < n} min(height[i], height[j]) * (j - i)。
//
// 算法框架：
//   对撞指针：l 从 0 开始，r 从 n-1 开始，每次移动矮边板向中间靠拢。
//
// 关键引理（移动矮边板的正确性）：
//   设当前状态 (l, r) 且 height[l] ≤ height[r]。
//   对任意 k ∈ (l, r)：area(l, k) = min(height[l], height[k])*(k-l)
//   ≤ height[l]*(k-l) < height[l]*(r-l) = area(l, r)。
//   因此所有 (l, k) 配对都不可能得到更大面积，可安全排除，将 l 右移。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 移动矮边板的正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
func MaxArea(height []int) int {
	left, right := 0, len(height)-1
	maxWater := 0

	for left < right {
		width := right - left
		if height[left] < height[right] {
			if height[left]*width > maxWater {
				maxWater = height[left] * width
			}
			left++
		} else {
			if height[right]*width > maxWater {
				maxWater = height[right] * width
			}
			right--
		}
	}

	return maxWater
}
