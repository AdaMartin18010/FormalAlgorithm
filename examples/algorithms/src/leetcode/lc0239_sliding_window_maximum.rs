//! LeetCode 239. 滑动窗口最大值
//!
//! 给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到最右侧。
//! 只可以看到窗口中的 k 个数字，返回滑动窗口中的最大值。
//!
//! 对标: LeetCode 239 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md

use std::collections::VecDeque;

/// 计算每个滑动窗口中的最大值。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为整数数组，长度 ∈ [1, 10^5]；`k` ∈ [1, len(nums)]；
///   nums[i] ∈ [-10^4, 10^4]。
/// - **后置条件 (Post)**：返回长度为 n - k + 1 的数组，其中 result[i] = max(nums[i..i+k-1])。
///
/// # 核心思路
///
/// 单调队列优化：维护一个双端队列，存储窗口中可能成为最大值的元素的索引。
/// 队列中的索引对应的值单调递减。
///
/// # 窗口不变式 WindowInvariant(right)
///
/// deque 中存储的索引均落在当前窗口 [right-k+1, right] 内。
/// deque 中对应的值严格单调递减：
///   nums[deque[0]] > nums[deque[1]] > ... > nums[deque[-1]]
///
/// **维护**：
/// - 初始队列为空。
/// - 扩展 right：
///   * 从队尾弹出所有满足 nums[deque[-1]] ≤ nums[right] 的索引
///     （这些元素不可能成为未来窗口的最大值）。
///   * 将 right 入队。
///   * 若 deque[0] 已不在当前窗口内（deque[0] ≤ right - k），从队首弹出。
/// - 当窗口形成后（right ≥ k-1），deque[0] 即为当前窗口最大值。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 摊还分析：每个元素最多入队一次、出队一次。
/// - **空间复杂度**：O(k) — 队列最多存储 k 个索引。
///
/// # 证明要点
///
/// - 单调队列正确性见 `docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md`
/// - 核心：队首始终为当前窗口最大值；队尾淘汰策略保证任何被移出的元素
///   不可能成为后续窗口的最大值。
pub fn max_sliding_window(nums: Vec<i32>, k: i32) -> Vec<i32> {
    if nums.is_empty() || k == 0 {
        return Vec::new();
    }

    let k = k as usize;
    let n = nums.len();
    let mut result: Vec<i32> = Vec::with_capacity(n - k + 1);
    let mut deque: VecDeque<usize> = VecDeque::new();

    for right in 0..n {
        // 移除队尾不大于当前值的元素（它们不可能成为后续窗口的最大值）
        while let Some(&back) = deque.back() {
            if nums[back] <= nums[right] {
                deque.pop_back();
            } else {
                break;
            }
        }

        deque.push_back(right);

        // 移除队首不在窗口内的元素
        if let Some(&front) = deque.front() {
            if front + k <= right {
                deque.pop_front();
            }
        }

        // 窗口已形成，记录最大值
        if right >= k - 1 {
            if let Some(&front) = deque.front() {
                result.push(nums[front]);
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(
            max_sliding_window(vec![1, 3, -1, -3, 5, 3, 6, 7], 3),
            vec![3, 3, 5, 5, 6, 7]
        );
    }

    #[test]
    fn test_example_2() {
        assert_eq!(max_sliding_window(vec![1], 1), vec![1]);
    }

    #[test]
    fn test_k_equals_n() {
        assert_eq!(max_sliding_window(vec![1, 2, 3, 4], 4), vec![4]);
    }

    #[test]
    fn test_increasing() {
        assert_eq!(
            max_sliding_window(vec![1, 2, 3, 4, 5], 2),
            vec![2, 3, 4, 5]
        );
    }

    #[test]
    fn test_decreasing() {
        assert_eq!(
            max_sliding_window(vec![5, 4, 3, 2, 1], 2),
            vec![5, 4, 3, 2]
        );
    }

    #[test]
    fn test_all_same() {
        assert_eq!(
            max_sliding_window(vec![5, 5, 5, 5], 2),
            vec![5, 5, 5]
        );
    }

    #[test]
    fn test_negative() {
        assert_eq!(
            max_sliding_window(vec![-1, -3, -5, -2], 2),
            vec![-1, -3, -2]
        );
    }
}
