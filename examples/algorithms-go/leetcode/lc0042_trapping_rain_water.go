// LeetCode 42. Trapping Rain Water
// 链接: https://leetcode.com/problems/trapping-rain-water/
// 难度: Hard
//
// 题目描述:
// 给定 n 个非负整数表示每个宽度为 1 的柱子的高度图，计算按此排列的柱子，下雨之后能接多少雨水。
//
// 形式化规约:
//   输入: height ∈ N^n
//   输出: Σ_i max(0, min(max_{j≤i} height[j], max_{j≥i} height[j]) - height[i])
//
// 最优解思路:
//   双指针优化：维护左侧最大高度 left_max 和右侧最大高度 right_max。
//   若 left_max < right_max，则左侧当前位置的积水量由 left_max 决定（右侧有更高的墙保证不泄漏），移动左指针；
//   否则移动右指针。
//
// 复杂度:
//   时间: O(n)
//   空间: O(1)
//
// 正确性要点:
//   每个位置 i 的积水量取决于左右最高墙的较小值：
//   water[i] = max(0, min(left_max, right_max) - height[i])
//   双指针的正确性在于：当 left_max < right_max 时，左指针处的积水量已确定，可以放心计算并移动。

package leetcode

func trap(height []int) int {
	left, right := 0, len(height)-1
	leftMax, rightMax := 0, 0
	water := 0

	for left < right {
		if height[left] < height[right] {
			if height[left] >= leftMax {
				leftMax = height[left]
			} else {
				water += leftMax - height[left]
			}
			left++
		} else {
			if height[right] >= rightMax {
				rightMax = height[right]
			} else {
				water += rightMax - height[right]
			}
			right--
		}
	}

	return water
}

// TestTrappingRainWater 测试接雨水函数
func TestTrappingRainWater() {
	// 示例 1
	h1 := []int{0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1}
	if trap(h1) != 6 {
		panic("Test 1 failed")
	}
	// 示例 2
	h2 := []int{4, 2, 0, 3, 2, 5}
	if trap(h2) != 9 {
		panic("Test 2 failed")
	}
	// 边界: 空数组
	if trap([]int{}) != 0 {
		panic("Test empty failed")
	}
	// 边界: 单调递增
	h3 := []int{0, 1, 2, 3, 4}
	if trap(h3) != 0 {
		panic("Test ascending failed")
	}
}
