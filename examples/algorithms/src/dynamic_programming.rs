//! # 动态规划算法 / Dynamic Programming Algorithms
//!
//! 实现经典动态规划算法及其形式化规范。

/// 最长公共子序列 (LCS) / Longest Common Subsequence
///
/// # 形式化定义 / Formal Definition
///
/// 给定两个序列 X = ⟨x₁, x₂, ..., xₘ⟩ 和 Y = ⟨y₁, y₂, ..., yₙ⟩，
/// 找到它们的最长公共子序列 Z = ⟨z₁, z₂, ..., zₖ⟩。
///
/// ## 递归定义 / Recursive Definition
///
/// 设 c[i,j] 为 X[1..i] 和 Y[1..j] 的 LCS 长度，则：
///
/// ```text
/// c[i,j] = ⎧ 0                           如果 i = 0 或 j = 0
///          ⎨ c[i-1,j-1] + 1              如果 i,j > 0 且 xᵢ = yⱼ
///          ⎩ max(c[i-1,j], c[i,j-1])    如果 i,j > 0 且 xᵢ ≠ yⱼ
/// ```
///
/// ## 最优子结构 / Optimal Substructure
/// - LCS(X[1..i], Y[1..j]) 的解包含 LCS(X[1..i-1], Y[1..j-1]) 的解
///
/// ## 重叠子问题 / Overlapping Subproblems
/// - 相同的子问题会被重复计算，因此适合用动态规划
///
/// ## 时间复杂度 / Time Complexity
/// - O(m × n) - m 和 n 分别是两个序列的长度
///
/// ## 空间复杂度 / Space Complexity
/// - O(m × n) - 存储DP表
/// - 可优化至 O(min(m, n))
///
/// # 参考文献 / References
/// - [CLRS2009] Cormen et al., "Introduction to Algorithms", 第3版, 第15.4节
/// - 对应文档: `docs/09-算法理论/02-算法设计范式/02-动态规划.md`
///
/// # Examples
///
/// ```
/// use algorithms::dynamic_programming::longest_common_subsequence;
///
/// let x = "ABCDGH";
/// let y = "AEDFHR";
/// let (length, lcs) = longest_common_subsequence(x, y);
/// assert_eq!(length, 3); // "ADH"
/// ```
pub fn longest_common_subsequence(x: &str, y: &str) -> (usize, String) {
    let x_chars: Vec<char> = x.chars().collect();
    let y_chars: Vec<char> = y.chars().collect();
    let m = x_chars.len();
    let n = y_chars.len();
    
    // 创建DP表
    let mut c = vec![vec![0; n + 1]; m + 1];
    
    // 填充DP表
    for i in 1..=m {
        for j in 1..=n {
            if x_chars[i - 1] == y_chars[j - 1] {
                c[i][j] = c[i - 1][j - 1] + 1;
            } else {
                c[i][j] = std::cmp::max(c[i - 1][j], c[i][j - 1]);
            }
        }
    }
    
    // 回溯构造LCS
    let lcs = reconstruct_lcs(&c, &x_chars, &y_chars, m, n);
    
    (c[m][n], lcs)
}

/// 回溯构造LCS字符串
fn reconstruct_lcs(
    c: &[Vec<usize>],
    x: &[char],
    y: &[char],
    i: usize,
    j: usize,
) -> String {
    if i == 0 || j == 0 {
        return String::new();
    }
    
    if x[i - 1] == y[j - 1] {
        let mut lcs = reconstruct_lcs(c, x, y, i - 1, j - 1);
        lcs.push(x[i - 1]);
        lcs
    } else if c[i - 1][j] > c[i][j - 1] {
        reconstruct_lcs(c, x, y, i - 1, j)
    } else {
        reconstruct_lcs(c, x, y, i, j - 1)
    }
}

/// 最长公共子序列（空间优化版）/ LCS (Space Optimized)
///
/// 只返回LCS长度，空间复杂度降至 O(min(m, n))
///
/// # Examples
///
/// ```
/// use algorithms::dynamic_programming::lcs_length;
///
/// let x = "ABCDGH";
/// let y = "AEDFHR";
/// assert_eq!(lcs_length(x, y), 3);
/// ```
pub fn lcs_length(x: &str, y: &str) -> usize {
    let x_chars: Vec<char> = x.chars().collect();
    let y_chars: Vec<char> = y.chars().collect();
    let m = x_chars.len();
    let n = y_chars.len();
    
    // 确保x是较短的序列
    let (shorter, longer) = if m <= n {
        (&x_chars, &y_chars)
    } else {
        (&y_chars, &x_chars)
    };
    
    let short_len = shorter.len();
    let long_len = longer.len();
    
    // 只需要两行的DP表
    let mut prev = vec![0; long_len + 1];
    let mut curr = vec![0; long_len + 1];
    
    for i in 1..=short_len {
        for j in 1..=long_len {
            if shorter[i - 1] == longer[j - 1] {
                curr[j] = prev[j - 1] + 1;
            } else {
                curr[j] = std::cmp::max(prev[j], curr[j - 1]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    
    prev[long_len]
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lcs_basic() {
        let (length, lcs) = longest_common_subsequence("ABCDGH", "AEDFHR");
        assert_eq!(length, 3);
        assert_eq!(lcs, "ADH");
    }
    
    #[test]
    fn test_lcs_empty() {
        let (length, lcs) = longest_common_subsequence("", "ABCD");
        assert_eq!(length, 0);
        assert_eq!(lcs, "");
    }
    
    #[test]
    fn test_lcs_same() {
        let (length, lcs) = longest_common_subsequence("ABCD", "ABCD");
        assert_eq!(length, 4);
        assert_eq!(lcs, "ABCD");
    }
    
    #[test]
    fn test_lcs_no_common() {
        let (length, lcs) = longest_common_subsequence("ABC", "DEF");
        assert_eq!(length, 0);
        assert_eq!(lcs, "");
    }
    
    #[test]
    fn test_lcs_length_optimized() {
        assert_eq!(lcs_length("ABCDGH", "AEDFHR"), 3);
        assert_eq!(lcs_length("", "ABCD"), 0);
        assert_eq!(lcs_length("ABCD", "ABCD"), 4);
    }
    
    #[test]
    fn test_lcs_consistency() {
        let test_cases = vec![
            ("AGGTAB", "GXTXAYB"),
            ("ABCDGH", "AEDFHR"),
            ("石の上にも三年", "石三年"),
        ];
        
        for (x, y) in test_cases {
            let (full_length, _) = longest_common_subsequence(x, y);
            let opt_length = lcs_length(x, y);
            assert_eq!(full_length, opt_length);
        }
    }
}

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn test_lcs_length_commutative(s1 in "[a-z]{0,20}", s2 in "[a-z]{0,20}") {
            let len1 = lcs_length(&s1, &s2);
            let len2 = lcs_length(&s2, &s1);
            assert_eq!(len1, len2);
        }
        
        #[test]
        fn test_lcs_length_bounds(s1 in "[a-z]{0,20}", s2 in "[a-z]{0,20}") {
            let len = lcs_length(&s1, &s2);
            assert!(len <= s1.len());
            assert!(len <= s2.len());
        }
        
        #[test]
        fn test_lcs_with_self(s in "[a-z]{0,20}") {
            let len = lcs_length(&s, &s);
            assert_eq!(len, s.len());
        }
    }
}

