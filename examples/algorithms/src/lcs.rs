//! 最长公共子序列（Longest Common Subsequence, LCS）实现
//!
//! LCS问题是动态规划的经典应用，用于找出两个序列的最长公共子序列。
//! 子序列不要求连续，但要求相对顺序一致。


/// 最长公共子序列结果
#[derive(Debug, Clone, PartialEq)]
pub struct LCSResult<T> {
    /// LCS的长度
    pub length: usize,
    /// LCS序列
    pub sequence: Vec<T>,
}

/// 计算最长公共子序列
///
/// # 算法说明
///
/// 使用动态规划求解：
/// - `dp[i][j]` 表示 `seq1[0..i]` 和 `seq2[0..j]` 的LCS长度
/// - 状态转移：
///   - 如果 `seq1[i-1] == seq2[j-1]`：`dp[i][j] = dp[i-1][j-1] + 1`
///   - 否则：`dp[i][j] = max(dp[i-1][j], dp[i][j-1])`
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m * n)，其中 m 和 n 是两个序列的长度
/// - **空间复杂度**：O(m * n) - 标准实现
///               O(min(m, n)) - 空间优化版本
///
/// # 参数
///
/// * `seq1` - 第一个序列
/// * `seq2` - 第二个序列
///
/// # 返回值
///
/// 返回 `LCSResult`，包含LCS的长度和序列
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs;
///
/// let seq1 = vec!['A', 'B', 'C', 'B', 'D', 'A', 'B'];
/// let seq2 = vec!['B', 'D', 'C', 'A', 'B', 'A'];
/// let result = lcs(&seq1, &seq2);
///
/// assert_eq!(result.length, 4);
/// // LCS可能不唯一，序列可以是 BCBA、BDAB等
/// assert_eq!(result.sequence.len(), 4);
/// ```
///
/// # 注意
///
/// LCS可能不唯一，本实现返回字典序较小的解
pub fn lcs<T: Clone + Eq + std::fmt::Debug>(seq1: &[T], seq2: &[T]) -> LCSResult<T> {
    let m = seq1.len();
    let n = seq2.len();

    // 处理空序列
    if m == 0 || n == 0 {
        return LCSResult {
            length: 0,
            sequence: vec![],
        };
    }

    // 构建DP表
    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            if seq1[i - 1] == seq2[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }

    // 回溯重建LCS
    let sequence = backtrack(&dp, seq1, seq2, m, n);

    LCSResult {
        length: dp[m][n],
        sequence,
    }
}

/// 仅计算LCS长度（空间优化版本）
///
/// 使用滚动数组，空间复杂度优化至 O(min(m, n))
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs::lcs_length;
///
/// let seq1 = "ABCBDAB";
/// let seq2 = "BDCABA";
/// let length = lcs_length(seq1.as_bytes(), seq2.as_bytes());
/// assert_eq!(length, 4);
/// ```
pub fn lcs_length<T: Eq>(seq1: &[T], seq2: &[T]) -> usize {
    let m = seq1.len();
    let n = seq2.len();

    if m == 0 || n == 0 {
        return 0;
    }

    // 确保 seq1 是较短的序列，节省空间
    let (seq1, seq2, m, n) = if m > n {
        (seq2, seq1, n, m)
    } else {
        (seq1, seq2, m, n)
    };

    let mut prev = vec![0; m + 1];
    let mut curr = vec![0; m + 1];

    for j in 1..=n {
        for i in 1..=m {
            if seq1[i - 1] == seq2[j - 1] {
                curr[i] = prev[i - 1] + 1;
            } else {
                curr[i] = curr[i - 1].max(prev[i]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[m]
}

/// 回溯重建LCS序列
fn backtrack<T: Clone + Eq>(
    dp: &[Vec<usize>],
    seq1: &[T],
    seq2: &[T],
    i: usize,
    j: usize,
) -> Vec<T> {
    let mut result = Vec::new();
    let mut i = i;
    let mut j = j;

    while i > 0 && j > 0 {
        if seq1[i - 1] == seq2[j - 1] {
            result.push(seq1[i - 1].clone());
            i -= 1;
            j -= 1;
        } else if dp[i - 1][j] > dp[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }

    result.reverse();
    result
}

/// 计算最长公共子串（连续）
///
/// 与LCS不同，子串要求字符连续
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m * n)
/// - **空间复杂度**：O(m * n)
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs::longest_common_substring;
///
/// let seq1 = "ABABC";
/// let seq2 = "BABCA";
/// let (substr, start1, start2) = longest_common_substring(seq1.as_bytes(), seq2.as_bytes());
///
/// assert_eq!(substr, "BABC".as_bytes());
/// assert_eq!(start1, 1);
/// assert_eq!(start2, 0);
/// ```
pub fn longest_common_substring<T: Clone + Eq>(
    seq1: &[T],
    seq2: &[T],
) -> (Vec<T>, usize, usize) {
    let m = seq1.len();
    let n = seq2.len();

    if m == 0 || n == 0 {
        return (vec![], 0, 0);
    }

    let mut dp = vec![vec![0; n + 1]; m + 1];
    let mut max_length = 0;
    let mut end_pos1 = 0;
    let mut end_pos2 = 0;

    for i in 1..=m {
        for j in 1..=n {
            if seq1[i - 1] == seq2[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
                if dp[i][j] > max_length {
                    max_length = dp[i][j];
                    end_pos1 = i;
                    end_pos2 = j;
                }
            }
        }
    }

    let start_pos1 = end_pos1 - max_length;
    let start_pos2 = end_pos2 - max_length;
    let substring = seq1[start_pos1..end_pos1].to_vec();

    (substring, start_pos1, start_pos2)
}

/// 计算编辑距离（Levenshtein Distance）
///
/// 将一个序列转换为另一个序列所需的最少操作次数（插入、删除、替换）
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m * n)
/// - **空间复杂度**：O(min(m, n))
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs::edit_distance;
///
/// let seq1 = "kitten";
/// let seq2 = "sitting";
/// let distance = edit_distance(seq1.as_bytes(), seq2.as_bytes());
/// assert_eq!(distance, 3); // kitten -> sitten -> sittin -> sitting
/// ```
pub fn edit_distance<T: Eq>(seq1: &[T], seq2: &[T]) -> usize {
    let m = seq1.len();
    let n = seq2.len();

    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // 确保 seq1 是较短的序列
    let (seq1, seq2, m, n) = if m > n {
        (seq2, seq1, n, m)
    } else {
        (seq1, seq2, m, n)
    };

    let mut prev = vec![0; m + 1];
    let mut curr = vec![0; m + 1];

    for i in 0..=m {
        prev[i] = i;
    }

    for j in 1..=n {
        curr[0] = j;
        for i in 1..=m {
            let cost = if seq1[i - 1] == seq2[j - 1] { 0 } else { 1 };
            curr[i] = (prev[i] + 1) // 删除
                .min(curr[i - 1] + 1) // 插入
                .min(prev[i - 1] + cost); // 替换
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[m]
}

/// 计算序列相似度（基于LCS）
///
/// 返回 0.0 到 1.0 之间的相似度，1.0 表示完全相同
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs::similarity;
///
/// let seq1 = "ABCBDAB";
/// let seq2 = "BDCABA";
/// let sim = similarity(seq1.as_bytes(), seq2.as_bytes());
/// // LCS长度是4，最大序列长度是7，相似度 = 4/7 ≈ 0.57
/// assert!((sim - 4.0/7.0).abs() < 0.01);
/// ```
pub fn similarity<T: Eq>(seq1: &[T], seq2: &[T]) -> f64 {
    if seq1.is_empty() && seq2.is_empty() {
        return 1.0;
    }
    if seq1.is_empty() || seq2.is_empty() {
        return 0.0;
    }

    let lcs_len = lcs_length(seq1, seq2);
    let max_len = seq1.len().max(seq2.len());
    
    lcs_len as f64 / max_len as f64
}

/// 查找所有LCS（可能有多个）
///
/// 当存在多个相同长度的LCS时，返回所有可能的解
///
/// # 注意
///
/// 当序列较长时，可能的LCS数量呈指数增长，请谨慎使用
///
/// # 示例
///
/// ```
/// use formal_algorithms::lcs::find_all_lcs;
///
/// let seq1 = vec!['A', 'B', 'C'];
/// let seq2 = vec!['A', 'C', 'B'];
/// let all_lcs = find_all_lcs(&seq1, &seq2);
///
/// assert!(all_lcs.contains(&vec!['A', 'B']));
/// assert!(all_lcs.contains(&vec!['A', 'C']));
/// ```
pub fn find_all_lcs<T: Clone + Eq + std::hash::Hash>(seq1: &[T], seq2: &[T]) -> Vec<Vec<T>> {
    let m = seq1.len();
    let n = seq2.len();

    if m == 0 || n == 0 {
        return vec![vec![]];
    }

    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            if seq1[i - 1] == seq2[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }

    let mut result = Vec::new();
    let mut current = Vec::new();
    backtrack_all(&dp, seq1, seq2, m, n, &mut current, &mut result);
    
    result
}

fn backtrack_all<T: Clone + Eq + std::hash::Hash>(
    dp: &[Vec<usize>],
    seq1: &[T],
    seq2: &[T],
    i: usize,
    j: usize,
    current: &mut Vec<T>,
    result: &mut Vec<Vec<T>>,
) {
    if i == 0 || j == 0 {
        let mut path = current.clone();
        path.reverse();
        result.push(path);
        return;
    }

    if seq1[i - 1] == seq2[j - 1] {
        current.push(seq1[i - 1].clone());
        backtrack_all(dp, seq1, seq2, i - 1, j - 1, current, result);
        current.pop();
    } else {
        if dp[i - 1][j] >= dp[i][j - 1] {
            backtrack_all(dp, seq1, seq2, i - 1, j, current, result);
        }
        if dp[i][j - 1] >= dp[i - 1][j] {
            backtrack_all(dp, seq1, seq2, i, j - 1, current, result);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_sequences() {
        let seq1: Vec<i32> = vec![];
        let seq2 = vec![1, 2, 3];
        let result = lcs(&seq1, &seq2);
        assert_eq!(result.length, 0);
        assert!(result.sequence.is_empty());
    }

    #[test]
    fn test_identical_sequences() {
        let seq1 = vec![1, 2, 3, 4, 5];
        let seq2 = vec![1, 2, 3, 4, 5];
        let result = lcs(&seq1, &seq2);
        assert_eq!(result.length, 5);
        assert_eq!(result.sequence, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_no_common() {
        let seq1 = vec![1, 2, 3];
        let seq2 = vec![4, 5, 6];
        let result = lcs(&seq1, &seq2);
        assert_eq!(result.length, 0);
    }

    #[test]
    fn test_classic_example() {
        let seq1 = vec!['A', 'B', 'C', 'B', 'D', 'A', 'B'];
        let seq2 = vec!['B', 'D', 'C', 'A', 'B', 'A'];
        let result = lcs(&seq1, &seq2);
        assert_eq!(result.length, 4);
        // LCS可能不唯一，只验证长度和有效性
        assert!(result.sequence.len() == 4);
        // 验证结果确实是公共子序列
        assert!(is_subsequence(&result.sequence, &seq1));
        assert!(is_subsequence(&result.sequence, &seq2));
    }

    // 辅助函数：检查sub是否是seq的子序列
    fn is_subsequence<T: Eq>(sub: &[T], seq: &[T]) -> bool {
        if sub.is_empty() {
            return true;
        }
        let mut i = 0;
        for item in seq {
            if i < sub.len() && *item == sub[i] {
                i += 1;
            }
        }
        i == sub.len()
    }

    #[test]
    fn test_lcs_length_only() {
        let seq1 = "ABCBDAB";
        let seq2 = "BDCABA";
        let length = lcs_length(seq1.as_bytes(), seq2.as_bytes());
        assert_eq!(length, 4);
    }

    #[test]
    fn test_longest_common_substring() {
        let seq1 = "ABABC";
        let seq2 = "BABCA";
        let (substr, start1, start2) = longest_common_substring(seq1.as_bytes(), seq2.as_bytes());
        assert_eq!(substr, "BABC".as_bytes());
        assert_eq!(start1, 1);
        assert_eq!(start2, 0);
    }

    #[test]
    fn test_edit_distance() {
        assert_eq!(edit_distance("".as_bytes(), "".as_bytes()), 0);
        assert_eq!(edit_distance("abc".as_bytes(), "".as_bytes()), 3);
        assert_eq!(edit_distance("".as_bytes(), "abc".as_bytes()), 3);
        assert_eq!(edit_distance("kitten".as_bytes(), "sitting".as_bytes()), 3);
        assert_eq!(edit_distance("sunday".as_bytes(), "saturday".as_bytes()), 3);
    }

    #[test]
    fn test_similarity() {
        assert_eq!(similarity("".as_bytes(), "".as_bytes()), 1.0);
        assert_eq!(similarity("abc".as_bytes(), "".as_bytes()), 0.0);
        // ABCBDAB(7) 和 BDCABA(6) 的LCS长度是4，相似度 = 4/7 ≈ 0.57
        let sim = similarity("ABCBDAB".as_bytes(), "BDCABA".as_bytes());
        assert!((sim - 4.0/7.0).abs() < 0.01, "Expected ~0.571, got {}", sim);
    }

    #[test]
    fn test_find_all_lcs() {
        let seq1 = vec!['A', 'B', 'C'];
        let seq2 = vec!['A', 'C', 'B'];
        let all_lcs = find_all_lcs(&seq1, &seq2);
        
        assert!(all_lcs.contains(&vec!['A', 'B']));
        assert!(all_lcs.contains(&vec!['A', 'C']));
    }

    #[test]
    fn test_lcs_with_strings() {
        let seq1 = vec!["apple", "banana", "cherry"];
        let seq2 = vec!["apple", "cherry", "date"];
        let result = lcs(&seq1, &seq2);
        assert_eq!(result.length, 2);
        assert_eq!(result.sequence, vec!["apple", "cherry"]);
    }

    #[test]
    fn test_lcs_length_space_optimized() {
        // 测试空间优化版本的正确性
        let seq1: Vec<i32> = (0..1000).collect();
        let mut seq2 = seq1.clone();
        seq2.reverse();
        
        let full_result = lcs(&seq1, &seq2);
        let length_only = lcs_length(&seq1, &seq2);
        
        assert_eq!(full_result.length, length_only);
    }
}
