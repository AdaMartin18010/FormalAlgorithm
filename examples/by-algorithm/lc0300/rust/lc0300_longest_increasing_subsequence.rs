//! LeetCode 300. 最长递增子序列 / Longest Increasing Subsequence
//!
//! 给你一个整数数组 nums，找到其中最长严格递增子序列的长度。
//!
//! 子序列是由数组派生而来的序列，删除（或不删除）数组中的元素而不改变其余元素的顺序。
//! 例如，[3,6,2,7] 是数组 [0,3,1,6,2,2,7] 的子序列。
//!
//! 题目链接: <https://leetcode.com/problems/longest-increasing-subsequence/>
//! 难度: Medium
//!
//! 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.3
//!
//! ## 形式化规约
//!
//! - **输入**: 整数数组 $nums[0..n-1]$
//! - **输出**: $\max \{ |S| : S \subseteq [0,n-1],\ \forall i < j \in S: nums[i] < nums[j] \}$
//! - **前置条件**: $1 \leq n \leq 2500$
//! - **后置条件**: 返回最长严格递增子序列的长度
//!
//! ## 解法一：$O(n^2)$ 标准 DP
//!
//! ### 状态转移方程
//!
//! $$ dp[i] = \max_{j < i,\ nums[j] < nums[i]} \{ dp[j] \} + 1 $$
//!
//! ### 最优子结构引理
//!
//! **引理**: 以 $nums[i]$ 结尾的最长递增子序列，其前缀必为某个以 $nums[j]$ ($j<i$, $nums[j]<nums[i]$)
//! 结尾的最长递增子序列加 $nums[i]$。
//!
//! **证明**: 反证法。若存在更长的前缀，则替换后得到更长的以 $nums[i]$ 结尾的递增子序列，矛盾。$\square$
//!
//! ## 解法二：$O(n \log n)$ 二分优化
//!
//! ### 核心思想
//!
//! 维护数组 `tails[k]` = 长度为 $k+1$ 的递增子序列的最小末尾元素。
//! `tails` 保持严格递增，可用二分查找维护。
//!
//! ### 正确性证明
//!
//! **引理** (tails 单调性): `tails` 数组始终保持严格递增。
//!
//! **证明**: 若存在 `tails[k] >= tails[k+1]`，则长度为 $k+2$ 的子序列去掉最后一个元素
//! 可得到长度为 $k+1$ 且末尾元素更小的子序列，与 `tails[k]` 的定义矛盾。$\square$

/// 最长递增子序列 — $O(n^2)$ 标准动态规划实现
///
/// # 参数
///
/// * `nums` - 整数数组
///
/// # 返回值
///
/// 最长严格递增子序列的长度。
///
/// # 复杂度分析
///
/// | 指标 | 值 | 说明 |
/// |------|-----|------|
/// | 时间复杂度 | $O(n^2)$ | 双重循环 |
/// | 空间复杂度 | $O(n)$ | dp 数组 |
pub fn length_of_lis_dp(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut dp = vec![1; n];
    let mut max_len = 1;
    for i in 1..n {
        for j in 0..i {
            if nums[j] < nums[i] {
                dp[i] = dp[i].max(dp[j] + 1);
            }
        }
        max_len = max_len.max(dp[i]);
    }
    max_len
}

/// 最长递增子序列 — $O(n \log n)$ 二分优化实现
///
/// # 参数
///
/// * `nums` - 整数数组
///
/// # 返回值
///
/// 最长严格递增子序列的长度。
///
/// # 复杂度分析
///
/// | 指标 | 值 | 说明 |
/// |------|-----|------|
/// | 时间复杂度 | $O(n \log n)$ | 每个元素二分查找 |
/// | 空间复杂度 | $O(n)$ | tails 数组（最坏情况） |
///
/// # 正确性证明
///
/// **定理**: `length_of_lis_binary` 返回最长严格递增子序列的长度。
///
/// **证明**:
///
/// 维护 `tails[l]` = 所有长度为 $l+1$ 的递增子序列中最小的末尾元素。
///
/// 1. **存在性**: `tails` 中的每个值都对应一个真实存在的递增子序列（由构造过程保证）。
/// 2. **最优性**: 对任意长度 $L$，若存在长度为 $L$ 的递增子序列，则 `tails[L-1]` 有定义。
///    因为 `tails[L-1]` 是长度为 $L$ 的子序列的最小末尾，只要存在长度为 $L$ 的子序列，
///    `tails[L-1]` 就必然 $\leq$ 该子序列的末尾元素。
/// 3. **长度不变性**: `tails` 的长度始终等于当前找到的最长递增子序列长度。
///
/// 因此最终 `tails.len()` 即为 LIS 长度。$\square$
pub fn length_of_lis_binary(nums: Vec<i32>) -> i32 {
    let mut tails: Vec<i32> = Vec::new();
    for &num in &nums {
        match tails.binary_search(&num) {
            Ok(_) => {} // 严格递增：不处理相等元素（即不替换，保持最早出现的较小值）
            Err(pos) => {
                if pos == tails.len() {
                    tails.push(num);
                } else {
                    tails[pos] = num;
                }
            }
        }
    }
    tails.len() as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let nums = vec![10, 9, 2, 5, 3, 7, 101, 18];
        assert_eq!(length_of_lis_dp(nums.clone()), 4);
        assert_eq!(length_of_lis_binary(nums), 4); // [2, 3, 7, 101]
    }

    #[test]
    fn test_example_2() {
        let nums = vec![0, 1, 0, 3, 2, 3];
        assert_eq!(length_of_lis_dp(nums.clone()), 4);
        assert_eq!(length_of_lis_binary(nums), 4); // [0, 1, 2, 3]
    }

    #[test]
    fn test_example_3() {
        let nums = vec![7, 7, 7, 7, 7, 7, 7];
        assert_eq!(length_of_lis_dp(nums.clone()), 1);
        assert_eq!(length_of_lis_binary(nums), 1);
    }

    #[test]
    fn test_single() {
        let nums = vec![1];
        assert_eq!(length_of_lis_dp(nums.clone()), 1);
        assert_eq!(length_of_lis_binary(nums), 1);
    }

    #[test]
    fn test_decreasing() {
        let nums = vec![5, 4, 3, 2, 1];
        assert_eq!(length_of_lis_dp(nums.clone()), 1);
        assert_eq!(length_of_lis_binary(nums), 1);
    }

    #[test]
    fn test_increasing() {
        let nums = vec![1, 2, 3, 4, 5];
        assert_eq!(length_of_lis_dp(nums.clone()), 5);
        assert_eq!(length_of_lis_binary(nums), 5);
    }

    #[test]
    fn test_equivalence() {
        // 验证两种方法结果一致
        let test_cases = vec![
            vec![10, 9, 2, 5, 3, 7, 101, 18],
            vec![0, 1, 0, 3, 2, 3],
            vec![7, 7, 7, 7, 7],
            vec![1, 3, 6, 7, 9, 4, 10, 5, 6],
            vec![3, 1, 2, 1, 8, 5, 6],
        ];
        for nums in test_cases {
            let dp_result = length_of_lis_dp(nums.clone());
            let binary_result = length_of_lis_binary(nums);
            assert_eq!(dp_result, binary_result, "Mismatch for {:?}", dp_result);
        }
    }
}
