//! LeetCode 516. 最长回文子序列
//!
//! 给你一个字符串 `s`，找出其中最长的回文子序列，并返回该序列的长度。
//!
//! # 核心思路
//!
//! **区间动态规划**：
//! - 设 `dp[i][j]` 表示子串 `s[i..=j]` 的最长回文子序列长度。
//! - 状态转移：
//!   - 若 `s[i] == s[j]`，则 `dp[i][j] = dp[i+1][j-1] + 2`（两端字符可纳入回文）。
//!   - 若 `s[i] != s[j]`，则 `dp[i][j] = max(dp[i+1][j], dp[i][j-1])`（舍去一端）。
//! - 边界：`dp[i][i] = 1`（单个字符）。
//!
//! # 复杂度分析
//!
//! - **时间复杂度**：O(n²) — 枚举区间长度和左端点。
//! - **空间复杂度**：O(n²) — 二维 DP 数组。

/// 计算字符串 `s` 的最长回文子序列长度。
pub fn longest_palindrome_subseq(s: String) -> i32 {
    let n = s.len();
    if n <= 1 {
        return n as i32;
    }
    let bytes = s.as_bytes();

    // dp[i][j] = s[i..=j] 的最长回文子序列长度
    let mut dp = vec![vec![0; n]; n];
    for i in 0..n {
        dp[i][i] = 1;
    }

    // 按区间长度从小到大枚举
    for length in 2..=n {
        for i in 0..=n - length {
            let j = i + length - 1;
            if bytes[i] == bytes[j] {
                dp[i][j] = if length == 2 {
                    2
                } else {
                    dp[i + 1][j - 1] + 2
                };
            } else {
                dp[i][j] = dp[i + 1][j].max(dp[i][j - 1]);
            }
        }
    }

    dp[0][n - 1]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(longest_palindrome_subseq("bbbab".to_string()), 4);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(longest_palindrome_subseq("cbbd".to_string()), 2);
    }

    #[test]
    fn test_single_char() {
        assert_eq!(longest_palindrome_subseq("a".to_string()), 1);
    }

    #[test]
    fn test_all_same() {
        assert_eq!(longest_palindrome_subseq("aaaa".to_string()), 4);
    }

    #[test]
    fn test_no_repeated() {
        assert_eq!(longest_palindrome_subseq("abc".to_string()), 1);
    }
}
