//! 后缀数组 (Suffix Array)
//!
//! 后缀数组是字符串处理中的重要数据结构，用于高效解决字符串匹配、
//! 最长重复子串等问题。
//!
//! # 算法复杂度
//! - 构建时间复杂度: O(n log n) - 倍增算法
//! - 空间复杂度: O(n)
//! - LCP数组计算: O(n) - Kasai算法
//!
//! # 应用场景
//! - 最长重复子串查找
//! - 字符串匹配
//! - 最长公共子串
//! - 不同子串计数

/// 后缀数组结构体
///
/// 包含排序后的后缀起始位置数组和LCP数组
#[derive(Debug, Clone)]
pub struct SuffixArray {
    /// 原始字符串
    text: String,
    /// sa[i] 表示排名第i的后缀的起始位置
    sa: Vec<usize>,
    /// rank[i] 表示从位置i开始的后缀的排名
    rank: Vec<usize>,
    /// lcp[i] 表示sa[i]和sa[i-1]的最长公共前缀长度
    lcp: Vec<usize>,
}

impl SuffixArray {
    /// 从字符串构建后缀数组
    ///
    /// # 参数
    /// - `text`: 输入字符串
    ///
    /// # 返回
    /// - 构建好的SuffixArray实例
    ///
    /// # 示例
    /// ```
    /// use algorithms::suffix_array::SuffixArray;
    /// let sa = SuffixArray::new("banana");
    /// ```
    pub fn new(text: &str) -> Self {
        let text = text.to_string();
        let n = text.len();
        
        if n == 0 {
            return Self {
                text,
                sa: vec![],
                rank: vec![],
                lcp: vec![],
            };
        }

        // 倍增算法构建后缀数组
        let (sa, rank) = Self::build_sa(&text);
        
        // 计算LCP数组
        let lcp = Self::build_lcp(&text, &sa, &rank);

        Self { text, sa, rank, lcp }
    }

    /// 倍增算法构建后缀数组
    ///
    /// 时间复杂度: O(n log n)
    /// 空间复杂度: O(n)
    fn build_sa(text: &str) -> (Vec<usize>, Vec<usize>) {
        let n = text.len();
        let bytes = text.as_bytes();
        
        // 初始: 按第一个字符排序
        let mut sa: Vec<usize> = (0..n).collect();
        let mut rank: Vec<usize> = bytes.iter().map(|&b| b as usize).collect();
        let mut tmp = vec![0; n];
        
        // k倍增: 先比较前k个字符，再比较后k个字符
        let mut k = 1;
        while k < n {
            // 按第二关键字排序(sa[i]+k的位置的rank)
            // 使用计数排序思想，按rank排序
            sa.sort_by(|&i, &j| {
                let ri = if i + k < n { rank[i + k] } else { 0 };
                let rj = if j + k < n { rank[j + k] } else { 0 };
                if ri != rj {
                    ri.cmp(&rj)
                } else {
                    let ri = if i < n { rank[i] } else { 0 };
                    let rj = if j < n { rank[j] } else { 0 };
                    ri.cmp(&rj)
                }
            });

            // 重新计算rank
            tmp[sa[0]] = 1;
            for i in 1..n {
                let prev = sa[i - 1];
                let curr = sa[i];
                let prev_rank1 = rank[prev];
                let curr_rank1 = rank[curr];
                let prev_rank2 = if prev + k < n { rank[prev + k] } else { 0 };
                let curr_rank2 = if curr + k < n { rank[curr + k] } else { 0 };
                
                tmp[curr] = tmp[prev] + if prev_rank1 != curr_rank1 || prev_rank2 != curr_rank2 { 1 } else { 0 };
            }
            
            std::mem::swap(&mut rank, &mut tmp);
            
            if rank[sa[n - 1]] == n {
                break; // 所有后缀排名都不同
            }
            
            k <<= 1;
        }
        
        // 转换为0-based rank
        for r in rank.iter_mut() {
            *r -= 1;
        }
        
        (sa, rank)
    }

    /// Kasai算法计算LCP数组
    ///
    /// LCP[i] = 后缀SA[i]与SA[i-1]的最长公共前缀长度
    /// 时间复杂度: O(n)
    ///
    /// # 参数
    /// - `text`: 原始字符串
    /// - `sa`: 后缀数组
    /// - `rank`: 排名数组
    fn build_lcp(text: &str, sa: &[usize], rank: &[usize]) -> Vec<usize> {
        let n = text.len();
        let bytes = text.as_bytes();
        let mut lcp = vec![0; n];
        let mut k = 0;

        for i in 0..n {
            if rank[i] == 0 {
                continue; // SA[0]没有前一个后缀
            }
            
            let j = sa[rank[i] - 1];
            
            // 从当前匹配位置继续比较
            while i + k < n && j + k < n && bytes[i + k] == bytes[j + k] {
                k += 1;
            }
            
            lcp[rank[i]] = k;
            
            // 为下一次迭代做准备，至少减少1
            if k > 0 {
                k -= 1;
            }
        }

        lcp
    }

    /// 获取后缀数组
    pub fn sa(&self) -> &[usize] {
        &self.sa
    }

    /// 获取排名数组
    pub fn rank(&self) -> &[usize] {
        &self.rank
    }

    /// 获取LCP数组
    pub fn lcp(&self) -> &[usize] {
        &self.lcp
    }

    /// 获取排名第i的后缀字符串
    pub fn suffix(&self, i: usize) -> Option<&str> {
        self.sa.get(i).map(|&pos| &self.text[pos..])
    }

    /// 查找最长重复子串
    ///
    /// 最长重复子串对应LCP数组中的最大值
    ///
    /// # 返回
    /// - `(长度, 子串)`: 最长重复子串的长度和内容
    ///
    /// # 复杂度
    /// - 时间复杂度: O(n) - 遍历LCP数组
    /// - 空间复杂度: O(1)
    ///
    /// # 示例
    /// ```
    /// use algorithms::suffix_array::SuffixArray;
    /// let sa = SuffixArray::new("banana");
    /// let (len, substr) = sa.longest_repeated_substring();
    /// assert_eq!(substr, "ana");
    /// ```
    pub fn longest_repeated_substring(&self) -> (usize, String) {
        if self.lcp.is_empty() {
            return (0, String::new());
        }

        let mut max_len = 0;
        let mut max_pos = 0;

        for (i, &len) in self.lcp.iter().enumerate() {
            if len > max_len {
                max_len = len;
                max_pos = self.sa[i];
            }
        }

        if max_len == 0 {
            (0, String::new())
        } else {
            (max_len, self.text[max_pos..max_pos + max_len].to_string())
        }
    }

    /// 查找所有至少出现k次的子串
    ///
    /// 子串出现次数 = LCP数组中连续>=该子串长度的个数 + 1
    ///
    /// # 参数
    /// - `k`: 最小出现次数
    ///
    /// # 返回
    /// - 满足条件的子串列表
    pub fn repeated_substrings_k_times(&self, k: usize) -> Vec<(String, usize)> {
        let mut result = Vec::new();
        if k <= 1 || self.sa.len() < k {
            return result;
        }

        // 使用滑动窗口，找连续k-1个LCP都>=某长度的窗口
        for window_size in k - 1..=self.sa.len() {
            for i in 0..=self.sa.len().saturating_sub(window_size) {
                let window = &self.lcp[i + 1..=i + window_size - 1];
                if let Some(&min_lcp) = window.iter().min() {
                    if min_lcp > 0 {
                        let pos = self.sa[i];
                        let substr = self.text[pos..pos + min_lcp].to_string();
                        if !result.iter().any(|(s, _)| s == &substr) {
                            result.push((substr, min_lcp));
                        }
                    }
                }
            }
        }

        result.sort_by(|a, b| b.1.cmp(&a.1));
        result.dedup_by(|a, b| a.0 == b.0);
        result
    }

    /// 统计不同子串的数量
    ///
    /// 所有子串数量 - 重复子串数量
    /// 利用公式: n*(n+1)/2 - sum(LCP)
    ///
    /// # 复杂度
    /// - 时间复杂度: O(n)
    /// - 空间复杂度: O(1)
    pub fn count_distinct_substrings(&self) -> usize {
        let n = self.text.len();
        let total = n * (n + 1) / 2;
        let duplicate: usize = self.lcp.iter().sum();
        total - duplicate
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_suffix_array() {
        let sa = SuffixArray::new("banana");
        // 后缀: banana, anana, nana, ana, na, a
        // 排序后: a, ana, anana, banana, na, nana
        assert_eq!(sa.sa(), &[5, 3, 1, 0, 4, 2]);
    }

    #[test]
    fn test_lcp() {
        let sa = SuffixArray::new("banana");
        // LCP: 0, 1, 3, 0, 0, 2
        // sa[0]=5:"a", lcp[0]=0
        // sa[1]=3:"ana", lcp[1]=1 ("a")
        // sa[2]=1:"anana", lcp[2]=3 ("ana")
        // ...
        assert_eq!(sa.lcp()[1], 1); // "a"是"a"和"ana"的LCP
        assert_eq!(sa.lcp()[2], 3); // "ana"是"ana"和"anana"的LCP
    }

    #[test]
    fn test_longest_repeated_substring() {
        let sa = SuffixArray::new("banana");
        let (len, substr) = sa.longest_repeated_substring();
        assert_eq!(len, 3);
        assert_eq!(substr, "ana");
    }

    #[test]
    fn test_longest_repeated_substring_abcab() {
        let sa = SuffixArray::new("abcab");
        let (len, substr) = sa.longest_repeated_substring();
        assert_eq!(len, 2);
        assert_eq!(substr, "ab");
    }

    #[test]
    fn test_count_distinct_substrings() {
        // "banana"的所有子串:
        // b, ba, ban, bana, banan, banana
        // a, an, ana, anan, anana (第2个a)
        // n, na, nan, nana
        // a, an, ana (第4个a)
        // n, na (第5个n)
        // a (第6个a)
        // 去重后需要计算
        let sa = SuffixArray::new("banana");
        let count = sa.count_distinct_substrings();
        assert_eq!(count, 15); // banana有15个不同子串
    }

    #[test]
    fn test_empty_string() {
        let sa = SuffixArray::new("");
        assert!(sa.sa().is_empty());
        assert!(sa.lcp().is_empty());
        let (len, _) = sa.longest_repeated_substring();
        assert_eq!(len, 0);
    }

    #[test]
    fn test_single_char() {
        let sa = SuffixArray::new("a");
        assert_eq!(sa.sa(), &[0]);
        assert_eq!(sa.lcp(), &[0]);
        let (len, _) = sa.longest_repeated_substring();
        assert_eq!(len, 0);
    }

    #[test]
    fn test_all_same_chars() {
        let sa = SuffixArray::new("aaaa");
        let (len, substr) = sa.longest_repeated_substring();
        assert_eq!(len, 3); // "aaa"
        assert_eq!(substr, "aaa");
    }

    #[test]
    fn test_no_repeated_substring() {
        let sa = SuffixArray::new("abcd");
        let (len, _) = sa.longest_repeated_substring();
        assert_eq!(len, 0);
    }

    #[test]
    fn test_suffix_access() {
        let sa = SuffixArray::new("banana");
        assert_eq!(sa.suffix(0), Some("a"));
        assert_eq!(sa.suffix(1), Some("ana"));
        assert_eq!(sa.suffix(5), Some("nana"));
        assert_eq!(sa.suffix(6), None);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 基本用法
    pub fn example_basic_usage() {
        println!("=== 后缀数组基本用法 ===");
        
        let text = "banana";
        let sa = SuffixArray::new(text);
        
        println!("文本: {}", text);
        println!("后缀数组: {:?}", sa.sa());
        println!("LCP数组: {:?}", sa.lcp());
        
        println!("\n所有后缀:");
        for i in 0..sa.sa().len() {
            println!("  SA[{}] = {}: '{}' (LCP={})", 
                i, sa.sa()[i], sa.suffix(i).unwrap_or(""), sa.lcp()[i]);
        }
    }

    /// 示例2: 最长重复子串
    pub fn example_longest_repeated() {
        println!("\n=== 最长重复子串示例 ===");
        
        let text = "abcabcabc";
        let sa = SuffixArray::new(text);
        let (len, substr) = sa.longest_repeated_substring();
        
        println!("文本: {}", text);
        println!("最长重复子串: '{}' (长度={})", substr, len);
        
        let text2 = "abcdabcdefefef";
        let sa2 = SuffixArray::new(text2);
        let (len2, substr2) = sa2.longest_repeated_substring();
        println!("文本: {}", text2);
        println!("最长重复子串: '{}' (长度={})", substr2, len2);
    }

    /// 示例3: DNA序列分析
    pub fn example_dna_analysis() {
        println!("\n=== DNA序列分析示例 ===");
        
        let dna = "ATCGATCGATCG";
        let sa = SuffixArray::new(dna);
        
        println!("DNA序列: {}", dna);
        println!("不同子串数量: {}", sa.count_distinct_substrings());
        
        let (len, pattern) = sa.longest_repeated_substring();
        println!("最长重复模式: '{}' (长度={})", pattern, len);
    }
}
