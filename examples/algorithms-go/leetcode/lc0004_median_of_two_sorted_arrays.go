// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
package leetcode

import "math"

// FindMedianSortedArrays 寻找两个正序数组的中位数。
//
// 形式化规约：
//   Pre: nums1 和 nums2 各自按非降序排列，len(nums1)+len(nums2) >= 1。
//   Post: 返回两个数组合并后的中位数。
//
// 核心思路：
//   在较短的数组上进行二分查找分割点。
//
// 复杂度：
//   时间复杂度: O(log(min(m, n)))
//   空间复杂度: O(1)
func FindMedianSortedArrays(nums1 []int, nums2 []int) float64 {
	// 确保 nums1 是较短的数组
	if len(nums1) > len(nums2) {
		nums1, nums2 = nums2, nums1
	}

	m, n := len(nums1), len(nums2)
	totalLeft := (m + n + 1) / 2

	left, right := 0, m
	for left <= right {
		i := left + (right-left)/2
		j := totalLeft - i

		var nums1LeftMax, nums1RightMin float64
		if i == 0 {
			nums1LeftMax = math.Inf(-1)
		} else {
			nums1LeftMax = float64(nums1[i-1])
		}
		if i == m {
			nums1RightMin = math.Inf(1)
		} else {
			nums1RightMin = float64(nums1[i])
		}

		var nums2LeftMax, nums2RightMin float64
		if j == 0 {
			nums2LeftMax = math.Inf(-1)
		} else {
			nums2LeftMax = float64(nums2[j-1])
		}
		if j == n {
			nums2RightMin = math.Inf(1)
		} else {
			nums2RightMin = float64(nums2[j])
		}

		if nums1LeftMax <= nums2RightMin && nums2LeftMax <= nums1RightMin {
			if (m+n)%2 == 1 {
				return math.Max(nums1LeftMax, nums2LeftMax)
			}
			return (math.Max(nums1LeftMax, nums2LeftMax) + math.Min(nums1RightMin, nums2RightMin)) / 2.0
		} else if nums1LeftMax > nums2RightMin {
			right = i - 1
		} else {
			left = i + 1
		}
	}

	return 0.0
}
