//! 编辑距离 (Levenshtein Distance)
//! 
//! 动态规划实现，支持：
//! - 计算最小编辑距离
//! - 回溯编辑操作
//! - 空间优化版本

/// 计算编辑距离
/// 
/// 支持操作：插入、删除、替换（代价均为1）
/// 
/// # 复杂度
/// - 时间: O(|s1| * |s2|)
/// - 空间: O(min(|s1|, |s2|))
/// 
/// # 示例
/// ```
/// let dist = edit_distance("kitten", "sitting");
/// assert_eq!(dist, 3); // k→s, e→i, +g
/// ```
pub fn edit_distance(s1: &str, s2: &str) -> usize {
    let s1_bytes = s1.as_bytes();
    let s2_bytes = s2.as_bytes();
    
    // 确保s1是较短的，优化空间
    if s1_bytes.len() > s2_bytes.len() {
        return edit_distance(s2, s1);
    }
    
    let m = s1_bytes.len();
    let n = s2_bytes.len();
    
    // 只保留两行
    let mut prev = vec![0; m + 1];
    let mut curr = vec![0; m + 1];
    
    // 初始化第一行
    for j in 0..=m {
        prev[j] = j;
    }
    
    for i in 1..=n {
        curr[0] = i;
        for j in 1..=m {
            let cost = if s1_bytes[j - 1] == s2_bytes[i - 1] { 0 } else { 1 };
            
            curr[j] = std::cmp::min(
                std::cmp::min(
                    prev[j] + 1,      // 删除
                    curr[j - 1] + 1   // 插入
                ),
                prev[j - 1] + cost    // 替换/匹配
            );
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    
    prev[m]
}

/// 编辑操作
#[derive(Debug, Clone, PartialEq)]
pub enum EditOp {
    Match(char),
    Insert(char),
    Delete(char),
    Subst(char, char),  // (from, to)
}

/// 计算编辑距离并回溯操作序列
/// 
/// # 复杂度
/// - 时间: O(|s1| * |s2|)
/// - 空间: O(|s1| * |s2|)（需要完整DP表回溯）
pub fn edit_distance_with_ops(s1: &str, s2: &str) -> (usize, Vec<EditOp>) {
    let s1_chars: Vec<char> = s1.chars().collect();
    let s2_chars: Vec<char> = s2.chars().collect();
    
    let m = s1_chars.len();
    let n = s2_chars.len();
    
    // 完整DP表
    let mut dp = vec![vec![0; m + 1]; n + 1];
    
    // 初始化
    for j in 0..=m {
        dp[0][j] = j;
    }
    for i in 0..=n {
        dp[i][0] = i;
    }
    
    // 填充
    for i in 1..=n {
        for j in 1..=m {
            let cost = if s1_chars[j - 1] == s2_chars[i - 1] { 0 } else { 1 };
            
            dp[i][j] = std::cmp::min(
                std::cmp::min(
                    dp[i - 1][j] + 1,      // 删除 (从s1)
                    dp[i][j - 1] + 1       // 插入 (到s1)
                ),
                dp[i - 1][j - 1] + cost    // 替换/匹配
            );
        }
    }
    
    // 回溯
    let mut ops = Vec::new();
    let mut i = n;
    let mut j = m;
    
    while i > 0 || j > 0 {
        if i == 0 {
            // 只能插入
            ops.push(EditOp::Insert(s1_chars[j - 1]));
            j -= 1;
        } else if j == 0 {
            // 只能删除
            ops.push(EditOp::Delete(s2_chars[i - 1]));
            i -= 1;
        } else {
            let cost = if s1_chars[j - 1] == s2_chars[i - 1] { 0 } else { 1 };
            
            if dp[i][j] == dp[i - 1][j - 1] + cost {
                // 替换或匹配
                if cost == 0 {
                    ops.push(EditOp::Match(s1_chars[j - 1]));
                } else {
                    ops.push(EditOp::Subst(s1_chars[j - 1], s2_chars[i - 1]));
                }
                i -= 1;
                j -= 1;
            } else if dp[i][j] == dp[i][j - 1] + 1 {
                // 插入
                ops.push(EditOp::Insert(s1_chars[j - 1]));
                j -= 1;
            } else {
                // 删除
                ops.push(EditOp::Delete(s2_chars[i - 1]));
                i -= 1;
            }
        }
    }
    
    ops.reverse();
    (dp[n][m], ops)
}

/// 最长公共子序列 (LCS)
/// 
/// LCS长度 = (|s1| + |s2| - edit_distance) / 2
/// 
/// # 复杂度
/// - 时间: O(|s1| * |s2|)
/// - 空间: O(min(|s1|, |s2|))
pub fn lcs(s1: &str, s2: &str) -> String {
    let s1_chars: Vec<char> = s1.chars().collect();
    let s2_chars: Vec<char> = s2.chars().collect();
    
    let m = s1_chars.len();
    let n = s2_chars.len();
    
    // DP表
    let mut dp = vec![vec![0; m + 1]; n + 1];
    
    for i in 1..=n {
        for j in 1..=m {
            if s1_chars[j - 1] == s2_chars[i - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = std::cmp::max(dp[i - 1][j], dp[i][j - 1]);
            }
        }
    }
    
    // 回溯构造LCS
    let mut lcs = String::new();
    let mut i = n;
    let mut j = m;
    
    while i > 0 && j > 0 {
        if s1_chars[j - 1] == s2_chars[i - 1] {
            lcs.push(s1_chars[j - 1]);
            i -= 1;
            j -= 1;
        } else if dp[i - 1][j] > dp[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }
    
    // 反转（因为我们是从后往前构造的）
    lcs.chars().rev().collect()
}

/// 汉明距离 (Hamming Distance)
/// 
/// 要求两字符串等长，计算不同位置数
/// 
/// # Panics
/// 如果字符串长度不等则panic
pub fn hamming_distance(s1: &str, s2: &str) -> usize {
    assert_eq!(s1.len(), s2.len(), "Strings must have equal length for Hamming distance");
    
    s1.chars().zip(s2.chars()).filter(|(a, b)| a != b).count()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_edit_distance() {
        assert_eq!(edit_distance("kitten", "sitting"), 3);
        assert_eq!(edit_distance("", ""), 0);
        assert_eq!(edit_distance("abc", ""), 3);
        assert_eq!(edit_distance("", "abc"), 3);
        assert_eq!(edit_distance("abc", "abc"), 0);
        assert_eq!(edit_distance("horse", "ros"), 3);
    }
    
    #[test]
    fn test_edit_distance_with_ops() {
        let (dist, ops) = edit_distance_with_ops("kitten", "sitting");
        assert_eq!(dist, 3);
        
        // 验证操作序列
        let ops_str: Vec<String> = ops.iter().map(|op| match op {
            EditOp::Match(c) => format!("M({})", c),
            EditOp::Insert(c) => format!("I({})", c),
            EditOp::Delete(c) => format!("D({})", c),
            EditOp::Subst(a, b) => format!("S({},{})", a, b),
        }).collect();
        
        println!("Operations: {:?}", ops_str);
    }
    
    #[test]
    fn test_lcs() {
        assert_eq!(lcs("abcde", "ace"), "ace");
        assert_eq!(lcs("abc", "abc"), "abc");
        assert_eq!(lcs("abc", ""), "");
        assert_eq!(lcs("XMJYAUZ", "MZJAWXU"), "MJAU");
    }
    
    #[test]
    fn test_hamming_distance() {
        assert_eq!(hamming_distance("karolin", "kathrin"), 3);
        assert_eq!(hamming_distance("karolin", "karolin"), 0);
        assert_eq!(hamming_distance("1011101", "1001001"), 2);
    }
}
