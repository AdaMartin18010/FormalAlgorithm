//! LeetCode 1. 两数之和
//!
//! 给定一个整数数组 nums 和一个整数目标值 target，
//! 请你在该数组中找出和为目标值 target 的那两个整数，并返回它们的数组下标。
//!
//! 对标: LeetCode 1 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

use std::collections::HashMap;

/// 在数组中找出和为 target 的两个元素的索引。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 长度范围 `[2, 10^4]`，存在恰好一个满足条件的解。
/// - **后置条件 (Post)**：返回向量 `[i, j]` 满足 `i != j` 且 `nums[i] + nums[j] == target`。
///
/// # 核心思路
///
/// 使用哈希表记录已遍历元素值到索引的映射。
/// 对于当前元素 `nums[j]`，若 `target - nums[j]` 已在哈希表中，则找到配对。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 单次遍历数组。
/// - **空间复杂度**：O(n) — 哈希表最多存储 n 个元素。
///
/// # 证明要点
///
/// - 正确性：若解为 `(i, j)` 且 `i < j`，当遍历到 `j` 时，
///   `target - nums[j] = nums[i]` 已在哈希表中，故必能找到。
/// - 唯一性：题目保证恰好一个解。
pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
    let mut seen: HashMap<i32, i32> = HashMap::new();
    for (j, &num) in nums.iter().enumerate() {
        let complement = target - num;
        if let Some(&i) = seen.get(&complement) {
            return vec![i, j as i32];
        }
        seen.insert(num, j as i32);
    }
    vec![]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(two_sum(vec![2, 7, 11, 15], 9), vec![0, 1]);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(two_sum(vec![3, 2, 4], 6), vec![1, 2]);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(two_sum(vec![3, 3], 6), vec![0, 1]);
    }

    #[test]
    fn test_boundary_right() {
        assert_eq!(two_sum(vec![1, 2, 3, 4, 5], 9), vec![3, 4]);
    }

    #[test]
    fn test_negative_numbers() {
        assert_eq!(two_sum(vec![-1, -2, -3, -4, -5], -8), vec![2, 4]);
    }

    #[test]
    fn test_zeros() {
        assert_eq!(two_sum(vec![0, 4, 3, 0], 0), vec![0, 3]);
    }

    #[test]
    fn test_large_array() {
        let nums: Vec<i32> = (0..10_000).collect();
        assert_eq!(two_sum(nums, 19_997), vec![9998, 9999]);
    }
}
