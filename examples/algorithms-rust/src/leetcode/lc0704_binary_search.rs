//! LeetCode 704. 二分查找
//!
//! 给定一个 n 个元素有序的（升序）整型数组 nums 和一个目标值 target，
//! 写一个函数搜索 nums 中的 target，如果目标值存在返回下标，否则返回 -1。
//!
//! 对标: LeetCode 704 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md

/// 在有序数组中查找目标值的索引。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为升序排列，所有元素唯一（或按题意可重复），
///   且满足 `nums[i] ∈ [-10^4, 10^4]`，`len(nums) ∈ [0, 10^4]`。
/// - **后置条件 (Post)**：若 `∃ i, nums[i] == target`，返回该索引 `i`；否则返回 `-1`。
///
/// # 循环不变式
///
/// 设当前搜索区间为闭区间 `[left, right]`：
/// > 若 `target` 存在于 `nums` 中，则其索引必然落在 `[left, right]` 范围内。
///
/// **维护**：
/// - 初始时 `left = 0`，`right = n - 1`，不变式显然成立。
/// - 每次取 `mid = left + (right - left) / 2`：
///   - 若 `nums[mid] == target`，已找到，直接返回。
///   - 若 `nums[mid] < target`，则 `target` 若在数组中必在右半区间，令 `left = mid + 1`。
///   - 若 `nums[mid] > target`，则 `target` 若在数组中必在左半区间，令 `right = mid - 1`。
/// - 以上操作保持区间仍包含可能的目标索引。
///
/// **终止推出**：当 `left > right` 时区间为空，由不变式知 `target` 不在数组中，返回 `-1`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n) — 每次迭代将搜索区间长度减半。
/// - **空间复杂度**：O(1) — 仅使用 `left`、`right`、`mid` 三个标量变量。
///
/// # 证明要点
///
/// - 正确性证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md`
/// - 终止性：区间长度 `right - left + 1` 每轮严格递减，故必在有限步内使 `left > right`。
pub fn search(nums: Vec<i32>, target: i32) -> i32 {
    let mut left: i32 = 0;
    let mut right: i32 = nums.len() as i32 - 1;

    while left <= right {
        let mid = left + (right - left) / 2;
        let mid_val = nums[mid as usize];

        if mid_val == target {
            return mid;
        }

        if mid_val < target {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    -1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let nums = vec![-1, 0, 3, 5, 9, 12];
        assert_eq!(search(nums, 9), 4);
    }

    #[test]
    fn test_leetcode_example_2() {
        let nums = vec![-1, 0, 3, 5, 9, 12];
        assert_eq!(search(nums, 2), -1);
    }

    #[test]
    fn test_empty_array() {
        assert_eq!(search(vec![], 1), -1);
    }

    #[test]
    fn test_single_element_found() {
        assert_eq!(search(vec![5], 5), 0);
    }

    #[test]
    fn test_single_element_not_found() {
        assert_eq!(search(vec![5], 1), -1);
    }

    #[test]
    fn test_all_same_elements_found() {
        assert_eq!(search(vec![2, 2, 2, 2], 2), 1); // 任意一个索引均可
    }

    #[test]
    fn test_all_same_elements_not_found() {
        assert_eq!(search(vec![2, 2, 2, 2], 3), -1);
    }

    #[test]
    fn test_target_at_left_boundary() {
        assert_eq!(search(vec![1, 2, 3, 4, 5], 1), 0);
    }

    #[test]
    fn test_target_at_right_boundary() {
        assert_eq!(search(vec![1, 2, 3, 4, 5], 5), 4);
    }

    #[test]
    fn test_large_array() {
        let nums: Vec<i32> = (0..10_000).collect();
        assert_eq!(search(nums.clone(), 5_000), 5_000);
        assert_eq!(search(nums, 10_001), -1);
    }
}
