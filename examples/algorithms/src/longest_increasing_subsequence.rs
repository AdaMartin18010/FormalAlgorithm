//! 最长递增子序列（LIS）实现
//!
//! 最长递增子序列问题是动态规划的经典模型：
//! 给定一个序列，找出其中最长的严格递增子序列的长度。
//!
//! 对标: CLRS 4th Ed. 习题 14.4-6；MIT 6.006 Dynamic Programming 模块；
//! Stanford CS161、CMU 15-451 核心教学内容。
//!
//! ## 动态规划解法（O(n²)）
//!
//! `dp[i]` = 以第 i 个元素结尾的最长递增子序列的长度
//!
//! 状态转移：`dp[i] = max(dp[j] + 1)` 对所有 `j < i` 且 `arr[j] < arr[i]`
//!
//! ## 二分优化解法（O(n log n)）
//!
//! 维护一个数组 `tails[k]` = 长度为 k+1 的递增子序列的最小末尾元素。
//! 对于每个元素，在 `tails` 中二分查找第一个大于等于它的位置并替换。
//!
//! ## 复杂度对比
//!
//! | 解法 | 时间复杂度 | 空间复杂度 | 是否可还原序列 |
//! |------|----------|----------|-------------|
//! | DP | O(n²) | O(n) | ✅ |
//! | 二分优化 | O(n log n) | O(n) | ✅（需额外记录） |
//!
//! ## 应用
//!
//! -  patience sorting（纸牌排序）
//! -  双调欧几里得旅行商问题
//! -  DAG 中最长路径的简化版

/// 最长递增子序列长度（O(n²) 动态规划）
///
/// # 参数
///
/// * `arr` - 输入序列
///
/// # 返回值
///
/// 最长严格递增子序列的长度
///
/// # 示例
///
/// ```
/// use formal_algorithms::longest_increasing_subsequence::lis_length_dp;
///
/// let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
/// assert_eq!(lis_length_dp(&arr), 4); // [2, 3, 7, 101] 或 [2, 5, 7, 101]
/// ```
pub fn lis_length_dp(arr: &[i32]) -> usize {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let mut dp = vec![1; n];
    let mut max_len = 1;

    for i in 1..n {
        for j in 0..i {
            if arr[j] < arr[i] {
                dp[i] = dp[i].max(dp[j] + 1);
            }
        }
        max_len = max_len.max(dp[i]);
    }

    max_len
}

/// 最长递增子序列（O(n²) 动态规划，返回子序列本身）
///
/// # 返回值
///
/// 一个最长递增子序列
///
/// # 示例
///
/// ```
/// use formal_algorithms::longest_increasing_subsequence::lis_dp;
///
/// let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
/// let result = lis_dp(&arr);
/// assert_eq!(result.len(), 4);
/// // 验证结果是递增的
/// for i in 1..result.len() {
///     assert!(result[i - 1] < result[i]);
/// }
/// ```
pub fn lis_dp(arr: &[i32]) -> Vec<i32> {
    let n = arr.len();
    if n == 0 {
        return vec![];
    }

    let mut dp = vec![1; n];
    let mut prev = vec![None; n]; // 记录前驱节点

    let mut max_len = 1;
    let mut max_idx = 0;

    for i in 1..n {
        for j in 0..i {
            if arr[j] < arr[i] && dp[j] + 1 > dp[i] {
                dp[i] = dp[j] + 1;
                prev[i] = Some(j);
            }
        }
        if dp[i] > max_len {
            max_len = dp[i];
            max_idx = i;
        }
    }

    // 回溯构建子序列
    let mut result = Vec::new();
    let mut cur = Some(max_idx);
    while let Some(idx) = cur {
        result.push(arr[idx]);
        cur = prev[idx];
    }
    result.reverse();
    result
}

/// 最长递增子序列长度（O(n log n) 二分优化）
///
/// 使用 patience sorting 思想，维护 `tails` 数组。
///
/// # 示例
///
/// ```
/// use formal_algorithms::longest_increasing_subsequence::lis_length_binary;
///
/// let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
/// assert_eq!(lis_length_binary(&arr), 4);
/// ```
pub fn lis_length_binary(arr: &[i32]) -> usize {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let mut tails: Vec<i32> = Vec::new();

    for &num in arr {
        match tails.binary_search(&num) {
            Ok(pos) => {
                // 严格递增，相等的元素不能接在后面
                // 但我们需要替换以保持 tails 最小化
                tails[pos] = num;
            }
            Err(pos) => {
                if pos == tails.len() {
                    tails.push(num);
                } else {
                    tails[pos] = num;
                }
            }
        }
    }

    tails.len()
}

/// 最长递增子序列（O(n log n) 二分优化，返回子序列本身）
///
/// # 示例
///
/// ```
/// use formal_algorithms::longest_increasing_subsequence::lis_binary;
///
/// let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
/// let result = lis_binary(&arr);
/// assert_eq!(result.len(), 4);
/// for i in 1..result.len() {
///     assert!(result[i - 1] < result[i]);
/// }
/// ```
pub fn lis_binary(arr: &[i32]) -> Vec<i32> {
    let n = arr.len();
    if n == 0 {
        return vec![];
    }

    let mut tails: Vec<i32> = Vec::new();
    let mut tail_indices: Vec<usize> = Vec::new(); // tails[k] 对应原数组中的索引
    let mut prev = vec![None; n];

    for (i, &num) in arr.iter().enumerate() {
        let pos = match tails.binary_search(&num) {
            Ok(pos) => {
                tails[pos] = num;
                tail_indices[pos] = i;
                pos
            }
            Err(pos) => {
                if pos == tails.len() {
                    tails.push(num);
                    tail_indices.push(i);
                } else {
                    tails[pos] = num;
                    tail_indices[pos] = i;
                }
                pos
            }
        };

        if pos > 0 {
            prev[i] = Some(tail_indices[pos - 1]);
        }
    }

    // 回溯构建子序列
    let mut result = Vec::new();
    if let Some(&last_idx) = tail_indices.last() {
        let mut cur = Some(last_idx);
        while let Some(idx) = cur {
            result.push(arr[idx]);
            cur = prev[idx];
        }
        result.reverse();
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lis_length_basic() {
        let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
        assert_eq!(lis_length_dp(&arr), 4);
        assert_eq!(lis_length_binary(&arr), 4);
    }

    #[test]
    fn test_lis_empty() {
        let arr: Vec<i32> = vec![];
        assert_eq!(lis_length_dp(&arr), 0);
        assert_eq!(lis_length_binary(&arr), 0);
    }

    #[test]
    fn test_lis_single() {
        let arr = vec![5];
        assert_eq!(lis_length_dp(&arr), 1);
        assert_eq!(lis_length_binary(&arr), 1);
    }

    #[test]
    fn test_lis_strictly_increasing() {
        let arr = vec![1, 2, 3, 4, 5];
        assert_eq!(lis_length_dp(&arr), 5);
        assert_eq!(lis_length_binary(&arr), 5);
    }

    #[test]
    fn test_lis_strictly_decreasing() {
        let arr = vec![5, 4, 3, 2, 1];
        assert_eq!(lis_length_dp(&arr), 1);
        assert_eq!(lis_length_binary(&arr), 1);
    }

    #[test]
    fn test_lis_all_equal() {
        let arr = vec![3, 3, 3, 3];
        assert_eq!(lis_length_dp(&arr), 1); // 严格递增
        assert_eq!(lis_length_binary(&arr), 1);
    }

    #[test]
    fn test_lis_sequence() {
        let arr = vec![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];
        assert_eq!(lis_length_dp(&arr), 6);
        assert_eq!(lis_length_binary(&arr), 6);
    }

    #[test]
    fn test_lis_dp_returns_valid() {
        let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
        let result = lis_dp(&arr);
        assert_eq!(result.len(), 4);
        for i in 1..result.len() {
            assert!(result[i - 1] < result[i]);
        }
    }

    #[test]
    fn test_lis_binary_returns_valid() {
        let arr = vec![10, 9, 2, 5, 3, 7, 101, 18];
        let result = lis_binary(&arr);
        assert_eq!(result.len(), 4);
        for i in 1..result.len() {
            assert!(result[i - 1] < result[i]);
        }
    }

    #[test]
    fn test_dp_and_binary_agree() {
        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
        assert_eq!(lis_length_dp(&arr), lis_length_binary(&arr));
    }
}
