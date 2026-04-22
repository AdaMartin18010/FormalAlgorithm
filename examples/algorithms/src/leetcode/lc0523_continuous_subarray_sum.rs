//! LeetCode 523. 连续的子数组和
//!
//! 检查数组中是否存在连续子数组的大小至少为 2，且其和为 k 的倍数。
//!
//! 对标: LeetCode 523 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md

use std::collections::HashMap;

/// 检查是否存在长度至少为 2 且和可被 k 整除的连续子数组。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为整数数组，`k` 为整数。
/// - **后置条件 (Post)**：若存在长度 >= 2 且和 % k == 0 的连续子数组，返回 `true`。
///
/// # 核心思路
///
/// 前缀和 + 同余定理：
/// `k | S(l, r) ⇔ prefix[r+1] ≡ prefix[l] (mod k)`
/// 维护哈希表记录每个余数最早出现的位置。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n)`
/// - **空间复杂度**：`O(min(n, |k|))`
pub fn check_subarray_sum(nums: Vec<i32>, k: i32) -> bool {
    let n = nums.len();
    if n < 2 {
        return false;
    }

    // k = 0 特判
    if k == 0 {
        for i in 0..n - 1 {
            if nums[i] == 0 && nums[i + 1] == 0 {
                return true;
            }
        }
        return false;
    }

    let mut prefix = 0i64;
    let k64 = k as i64;
    let mut first_occurrence: HashMap<i64, usize> = HashMap::new();
    first_occurrence.insert(0, 0); // prefix[0] = 0 出现在位置 0

    for i in 0..n {
        prefix = ((prefix + nums[i] as i64) % k64 + k64) % k64;
        if let Some(&pos) = first_occurrence.get(&prefix) {
            if i + 1 - pos >= 2 {
                return true;
            }
        } else {
            first_occurrence.insert(prefix, i + 1);
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(check_subarray_sum(vec![23, 2, 4, 6, 7], 6));
    }

    #[test]
    fn test_example_2() {
        assert!(check_subarray_sum(vec![23, 2, 6, 4, 7], 6));
    }

    #[test]
    fn test_example_3() {
        assert!(!check_subarray_sum(vec![23, 2, 6, 4, 7], 13));
    }

    #[test]
    fn test_k_zero() {
        assert!(check_subarray_sum(vec![0, 0], 0));
        assert!(!check_subarray_sum(vec![0], 0));
    }

    #[test]
    fn test_minimum_length() {
        assert!(check_subarray_sum(vec![1, 1], 2));
    }
}
