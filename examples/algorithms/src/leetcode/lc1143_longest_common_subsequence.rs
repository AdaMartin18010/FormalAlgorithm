//! LeetCode 1143. 最长公共子序列
//!
//! 给定两个字符串 `text1` 和 `text2`，返回这两个字符串的最长公共子序列的长度。
//! 如果不存在公共子序列，返回 0。
//!
//! # 核心思路
//!
//! **经典双串动态规划**：
//! - 设 `dp[i][j]` 表示 `text1[0..i)` 与 `text2[0..j)` 的 LCS 长度。
//! - 状态转移：
//!   - 若 `text1[i-1] == text2[j-1]`，则 `dp[i][j] = dp[i-1][j-1] + 1`。
//!   - 否则 `dp[i][j] = max(dp[i-1][j], dp[i][j-1])`。
//! - 使用一维滚动数组优化空间。
//!
//! # 复杂度分析
//!
//! - **时间复杂度**：O(m·n)。
//! - **空间复杂度**：O(min(m, n)) — 滚动数组。

/// 计算两个字符串的最长公共子序列长度。
pub fn longest_common_subsequence(text1: String, text2: String) -> i32 {
    let (m, n) = (text1.len(), text2.len());
    if m == 0 || n == 0 {
        return 0;
    }

    // 让 text2 指向较短的字符串，优化空间
    let (s1, s2, m, n) = if m >= n {
        (text1, text2, m, n)
    } else {
        (text2, text1, n, m)
    };

    let b1 = s1.as_bytes();
    let b2 = s2.as_bytes();

    let mut dp = vec![0; n + 1];

    for i in 1..=m {
        let mut prev = 0; // 保存 dp[i-1][j-1]
        for j in 1..=n {
            let temp = dp[j]; // dp[i-1][j]
            if b1[i - 1] == b2[j - 1] {
                dp[j] = prev + 1;
            } else {
                dp[j] = dp[j].max(dp[j - 1]);
            }
            prev = temp;
        }
    }

    dp[n] as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(
            longest_common_subsequence("abcde".to_string(), "ace".to_string()),
            3
        );
    }

    #[test]
    fn test_example_2() {
        assert_eq!(
            longest_common_subsequence("abc".to_string(), "abc".to_string()),
            3
        );
    }

    #[test]
    fn test_example_3() {
        assert_eq!(
            longest_common_subsequence("abc".to_string(), "def".to_string()),
            0
        );
    }

    #[test]
    fn test_empty_string() {
        assert_eq!(longest_common_subsequence("".to_string(), "abc".to_string()), 0);
    }

    #[test]
    fn test_subsequence_in_middle() {
        assert_eq!(
            longest_common_subsequence("bsbininm".to_string(), "jmjkbkjkv".to_string()),
            1
        );
    }
}
