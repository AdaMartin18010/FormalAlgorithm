// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// ThreeSum 找出数组中所有和为 0 的不重复三元组。
//
// 形式化规约：
//   Pre: nums 为整数数组，长度 ∈ [0, 5000]。
//   Post: 返回所有满足 i < j < k 且 nums[i]+nums[j]+nums[k] == 0 的不重复三元组，
//         每个三元组内部按非降序排列。
//
// 算法框架：
//   1. 排序。
//   2. 固定 nums[i]，在右侧用对撞指针找两数之和为 -nums[i]。
//   3. 通过排序后的去重策略保证结果唯一性。
//
// 循环不变式（对撞指针）：
//   设固定 i，左指针 l = i+1，右指针 r = n-1。
//   所有满足 j < l 或 k > r 的配对均已被考察或不可能构成解。
//
//   维护：
//   - s == 0：记录解，收缩 l,r 跳过重复值。
//   - s < 0：nums[l] 太小，l++。
//   - s > 0：nums[r] 太大，r--。
//
// 复杂度：
//   时间复杂度: O(n^2)
//   空间复杂度: O(1)（不计输出空间）
//
// 证明要点：
//   - 不遗漏解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
func ThreeSum(nums []int) [][]int {
	n := len(nums)
	if n < 3 {
		return [][]int{}
	}

	// 简单插入排序（对于小规模或已近似有序数据效率可接受）
	// 实际工程实现建议使用 sort.Ints，但为保持教育目的展示排序概念
	for i := 1; i < n; i++ {
		key := nums[i]
		j := i - 1
		for j >= 0 && nums[j] > key {
			nums[j+1] = nums[j]
			j--
		}
		nums[j+1] = key
	}

	result := make([][]int, 0)

	for i := 0; i < n-2; i++ {
		if i > 0 && nums[i] == nums[i-1] {
			continue
		}

		if nums[i]+nums[i+1]+nums[i+2] > 0 {
			break
		}
		if nums[i]+nums[n-2]+nums[n-1] < 0 {
			continue
		}

		left, right := i+1, n-1
		for left < right {
			sum := nums[i] + nums[left] + nums[right]
			if sum == 0 {
				result = append(result, []int{nums[i], nums[left], nums[right]})
				for left < right && nums[left] == nums[left+1] {
					left++
				}
				for left < right && nums[right] == nums[right-1] {
					right--
				}
				left++
				right--
			} else if sum < 0 {
				left++
			} else {
				right--
			}
		}
	}

	return result
}
