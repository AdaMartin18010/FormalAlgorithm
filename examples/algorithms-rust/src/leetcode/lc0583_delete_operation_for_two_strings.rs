//! LeetCode 583. 两个字符串的删除操作
//!
//! 给定两个单词 `word1` 和 `word2`，找到使得 `word1` 和 `word2` 相同所需的最小步数，
//! 每步可以删除任意一个字符串中的一个字符。
//!
//! # 核心思路
//!
//! 关键观察：最终相等的字符串必然是 `word1` 和 `word2` 的某个公共子序列。
//! 为了使删除次数最少，应保留**最长公共子序列（LCS）**。
//!
//! 最小删除步数 = `len(word1) + len(word2) - 2 * LCS(word1, word2)`
//!
//! LCS 使用空间优化的一维 DP 求解。
//!
//! # 复杂度分析
//!
//! - **时间复杂度**：O(m·n)。
//! - **空间复杂度**：O(min(m, n)) — 滚动数组优化。

/// 计算使两个单词相同的最小删除步数。
pub fn min_distance(word1: String, word2: String) -> i32 {
    let (m, n) = (word1.len(), word2.len());
    if m == 0 {
        return n as i32;
    }
    if n == 0 {
        return m as i32;
    }

    // 确保 word2 是较短的，以优化空间
    let (s1, s2, m, n) = if m >= n {
        (word1, word2, m, n)
    } else {
        (word2, word1, n, m)
    };

    let b1 = s1.as_bytes();
    let b2 = s2.as_bytes();

    let mut dp = vec![0; n + 1];

    for i in 1..=m {
        let mut prev = 0; // dp[i-1][j-1]
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

    let lcs = dp[n];
    (m + n - 2 * lcs) as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(min_distance("sea".to_string(), "eat".to_string()), 2);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(min_distance("leetcode".to_string(), "etco".to_string()), 4);
    }

    #[test]
    fn test_one_empty() {
        assert_eq!(min_distance("".to_string(), "abc".to_string()), 3);
    }

    #[test]
    fn test_identical() {
        assert_eq!(min_distance("abc".to_string(), "abc".to_string()), 0);
    }

    #[test]
    fn test_no_common() {
        assert_eq!(min_distance("abc".to_string(), "def".to_string()), 6);
    }
}
