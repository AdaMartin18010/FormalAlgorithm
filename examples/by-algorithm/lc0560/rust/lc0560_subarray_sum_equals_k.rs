//! LeetCode 560. 和为 K 的子数组
//!
//! 给定一个整数数组和一个整数 k，找到该数组中和为 k 的连续子数组的个数。
//!
//! 对标: LeetCode 560 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md

use std::collections::HashMap;

/// 计算和为 k 的连续子数组的个数。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为整数数组，长度范围 `[1, 2·10^4]`；`k` 为整数。
/// - **后置条件 (Post)**：返回和恰好等于 `k` 的连续子数组的数量。
///
/// # 核心思路
///
/// 前缀和 + 哈希表：
/// `S(l, r) = prefix[r+1] - prefix[l] = k ⇔ prefix[r+1] = prefix[l] + k`
/// 遍历过程中，用哈希表记录已出现的前缀和频次。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n)` — 单次遍历。
/// - **空间复杂度**：`O(n)` — 哈希表最多存储 `n+1` 个前缀和。
///
/// # 证明要点
///
/// - 引理：`S(l, r) = prefix[r+1] - prefix[l]`（前缀和定义）。
/// - 引理：遍历到 `i` 时，哈希表包含 `prefix[0..i]` 的频次。
/// - 查询 `freq[prefix[i+1] - k]` 即统计所有以 `i` 结尾且和为 `k` 的子数组数。
pub fn subarray_sum(nums: Vec<i32>, k: i32) -> i32 {
    let mut count = 0;
    let mut prefix = 0;
    let mut freq: HashMap<i32, i32> = HashMap::new();
    freq.insert(0, 1); // 空前缀的和为 0，出现 1 次

    for num in nums {
        prefix += num;
        if let Some(&v) = freq.get(&(prefix - k)) {
            count += v;
        }
        *freq.entry(prefix).or_insert(0) += 1;
    }

    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(subarray_sum(vec![1, 1, 1], 2), 2);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(subarray_sum(vec![1, 2, 3], 3), 2);
    }

    #[test]
    fn test_all_zeros() {
        assert_eq!(subarray_sum(vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0), 55);
    }

    #[test]
    fn test_negative_numbers() {
        assert_eq!(subarray_sum(vec![-1, -1, 1], 0), 1);
    }

    #[test]
    fn test_mixed() {
        assert_eq!(subarray_sum(vec![1, -1, 0], 0), 3);
    }
}
