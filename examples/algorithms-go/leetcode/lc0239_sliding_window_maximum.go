package leetcode

// LeetCode 239. Sliding Window Maximum
// 滑动窗口最大值
//
// Return the max sliding window using a monotonically decreasing deque.

// MaxSlidingWindow 单调递减双端队列实现
// Monotonically decreasing deque
// Time: O(n), Space: O(k)
func MaxSlidingWindow(nums []int, k int) []int {
	dq := make([]int, 0)   // 存储索引，对应值单调递减 / Store indices
	res := make([]int, 0)

	for i, num := range nums {
		// 移除队尾小于当前值的元素 / Remove smaller elements from tail
		for len(dq) > 0 && nums[dq[len(dq)-1]] < num {
			dq = dq[:len(dq)-1]
		}
		dq = append(dq, i)

		// 移除已滑出窗口的队头 / Remove front out of window
		if dq[0] < i-k+1 {
			dq = dq[1:]
		}

		// 窗口已形成，记录最大值 / Record max when window formed
		if i >= k-1 {
			res = append(res, nums[dq[0]])
		}
	}

	return res
}
