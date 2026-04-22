//! LeetCode 239. Sliding Window Maximum
//! 滑动窗口最大值
//!
//! Return the max sliding window using a monotonically decreasing deque.

use std::collections::VecDeque;

/// 单调递减双端队列
/// Monotonically decreasing deque
/// Time: O(n), Space: O(k)
pub fn max_sliding_window(nums: Vec<i32>, k: i32) -> Vec<i32> {
    let k = k as usize;
    let mut dq: VecDeque<usize> = VecDeque::new();
    let mut res: Vec<i32> = Vec::new();

    for (i, &num) in nums.iter().enumerate() {
        // 移除队尾小于当前值的元素 / Remove smaller elements from tail
        while let Some(&back) = dq.back() {
            if nums[back] < num {
                dq.pop_back();
            } else {
                break;
            }
        }
        dq.push_back(i);

        // 移除已滑出窗口的队头 / Remove front out of window
        if dq[0] < i + 1 - k {
            dq.pop_front();
        }

        // 窗口已形成，记录最大值 / Record max when window formed
        if i >= k - 1 {
            res.push(nums[dq[0]]);
        }
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sliding_window_maximum() {
        assert_eq!(
            max_sliding_window(vec![1, 3, -1, -3, 5, 3, 6, 7], 3),
            vec![3, 3, 5, 5, 6, 7]
        );
        assert_eq!(max_sliding_window(vec![1], 1), vec![1]);
    }
}
