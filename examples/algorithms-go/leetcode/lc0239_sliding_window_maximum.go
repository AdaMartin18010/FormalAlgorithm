// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
package leetcode

// MaxSlidingWindow 计算每个滑动窗口中的最大值。
//
// 形式化规约：
//   Pre: nums 为整数数组，长度 ∈ [1, 10^5]；k ∈ [1, len(nums)]。
//   Post: 返回长度为 n-k+1 的数组，result[i] = max(nums[i..i+k-1])。
//
// 算法框架：
//   单调队列优化：维护双端队列存储可能成为最大值的元素索引，对应值单调递减。
//
// 窗口不变式：
//   deque 中索引均落在当前窗口 [right-k+1, right] 内。
//   nums[deque[0]] > nums[deque[1]] > ... > nums[deque[-1]]。
//
//   维护：
//   - 从队尾弹出所有 nums[deque[-1]] ≤ nums[right] 的索引。
//   - 将 right 入队。
//   - 若 deque[0] 已不在窗口内，从队首弹出。
//   - 当窗口形成后，deque[0] 即为当前窗口最大值。
//
// 复杂度：
//   时间复杂度: O(n) — 摊还分析：每个元素最多入队和出队各一次。
//   空间复杂度: O(k)
//
// 证明要点：
//   - 单调队列正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
func MaxSlidingWindow(nums []int, k int) []int {
	if len(nums) == 0 || k == 0 {
		return []int{}
	}

	n := len(nums)
	result := make([]int, 0, n-k+1)
	// 用切片模拟双端队列，存储索引
	deque := make([]int, 0, k)

	for right := 0; right < n; right++ {
		// 移除队尾不大于当前值的元素
		for len(deque) > 0 && nums[deque[len(deque)-1]] <= nums[right] {
			deque = deque[:len(deque)-1]
		}

		deque = append(deque, right)

		// 移除队首不在窗口内的元素
		if deque[0] <= right-k {
			deque = deque[1:]
		}

		// 窗口已形成，记录最大值
		if right >= k-1 {
			result = append(result, nums[deque[0]])
		}
	}

	return result
}
