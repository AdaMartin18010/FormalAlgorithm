//! Rabin-Karp字符串匹配算法
//!
//! Rabin-Karp算法使用滚动哈希技术进行字符串匹配，通过哈希值的比较来快速筛选不可能的匹配位置，
//! 只在哈希值匹配时才进行逐字符比较。特别适合多模式匹配和二维模式匹配。
//!
//! # 算法原理
//! 1. 计算模式串的哈希值
//! 2. 使用滚动哈希计算文本中每个子串的哈希值
//! 3. 比较哈希值，仅在匹配时进行逐字符验证
//!
//! # 滚动哈希公式
//! hash(s[0..m]) = (s[0]·b^(m-1) + s[1]·b^(m-2) + ... + s[m-1]) mod q
//!
//! # 时间复杂度
//! - 平均情况: O(n + m)
//! - 最坏情况: O(n·m)（哈希冲突较多时）
//! - 空间: O(1)
//!
//! # 适用场景
//! - 多模式匹配（同时搜索多个模式串）
//! - 抄袭检测
//! - DNA序列分析

/// 默认基数（通常选择一个大于字符集大小的素数）
const DEFAULT_BASE: u64 = 256;

/// 默认大素数（用于取模，减少哈希冲突）
const DEFAULT_MOD: u64 = 1_000_000_007;

/// Rabin-Karp字符串匹配器
pub struct RabinKarp {
    /// 哈希基数
    base: u64,
    /// 模数
    modulus: u64,
}

impl RabinKarp {
    /// 创建使用默认参数的匹配器
    pub fn new() -> Self {
        RabinKarp {
            base: DEFAULT_BASE,
            modulus: DEFAULT_MOD,
        }
    }

    /// 创建自定义参数的匹配器
    pub fn with_params(base: u64, modulus: u64) -> Self {
        RabinKarp { base, modulus }
    }

    /// 计算字符串的哈希值
    fn hash(&self, s: &str) -> u64 {
        let mut h: u64 = 0;
        for byte in s.bytes() {
            h = (h.wrapping_mul(self.base).wrapping_add(byte as u64)) % self.modulus;
        }
        h
    }

    /// 单模式匹配
    ///
    /// # 参数
    /// - `text`: 待搜索的文本
    /// - `pattern`: 模式串
    ///
    /// # 返回值
    /// 返回所有匹配位置的起始索引（0-based）
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::rabin_karp::RabinKarp;
    /// let rk = RabinKarp::new();
    /// let matches = rk.search("hello world", "world");
    /// assert_eq!(matches, vec![6]);
    /// ```
    pub fn search(&self, text: &str, pattern: &str) -> Vec<usize> {
        if pattern.is_empty() || text.len() < pattern.len() {
            return Vec::new();
        }

        let pattern_hash = self.hash(pattern);
        let m = pattern.len();
        let n = text.len();

        // 预计算 base^(m-1) % modulus
        let mut highest_power: u64 = 1;
        for _ in 0..m - 1 {
            highest_power = (highest_power * self.base) % self.modulus;
        }

        // 计算第一个窗口的哈希值
        let text_bytes = text.as_bytes();
        let mut window_hash: u64 = 0;
        for i in 0..m {
            window_hash = (window_hash.wrapping_mul(self.base).wrapping_add(text_bytes[i] as u64))
                % self.modulus;
        }

        let mut matches = Vec::new();

        // 滑动窗口
        for i in 0..=n - m {
            // 检查哈希值是否匹配
            if window_hash == pattern_hash {
                // 哈希匹配，验证实际字符串
                let substr = &text[i..i + m];
                if substr == pattern {
                    matches.push(i);
                }
            }

            // 计算下一个窗口的哈希值（滚动哈希）
            if i < n - m {
                // 移除最左边的字符
                window_hash = (window_hash + self.modulus
                    - ((text_bytes[i] as u64 * highest_power) % self.modulus))
                    % self.modulus;
                // 左移一位
                window_hash = (window_hash * self.base) % self.modulus;
                // 添加新字符
                window_hash = (window_hash + text_bytes[i + m] as u64) % self.modulus;
            }
        }

        matches
    }

    /// 多模式匹配
    ///
    /// 同时搜索多个模式串，返回每个模式串的所有匹配位置
    ///
    /// # 返回值
    /// Vec<(pattern_index, position)>
    pub fn search_multiple(&self, text: &str, patterns: &[&str]) -> Vec<(usize, usize)> {
        let mut all_matches = Vec::new();

        for (idx, pattern) in patterns.iter().enumerate() {
            let matches = self.search(text, pattern);
            for pos in matches {
                all_matches.push((idx, pos));
            }
        }

        // 按位置排序
        all_matches.sort_by_key(|&(_, pos)| pos);
        all_matches
    }

    /// 搜索任意一个模式（返回第一个匹配的）
    pub fn search_any(&self, text: &str, patterns: &[&str]) -> Option<(usize, usize)> {
        for (idx, pattern) in patterns.iter().enumerate() {
            if let Some(pos) = self.search(text, pattern).into_iter().next() {
                return Some((idx, pos));
            }
        }
        None
    }

    /// 计算两个字符串的相似度（用于抄袭检测）
    ///
    /// 使用k-gram指纹计算相似度
    pub fn similarity(&self, text1: &str, text2: &str, k: usize) -> f64 {
        if k == 0 || text1.len() < k || text2.len() < k {
            return 0.0;
        }

        let mut set1 = std::collections::HashSet::new();
        let mut set2 = std::collections::HashSet::new();

        // 提取text1的所有k-gram哈希
        for i in 0..=text1.len() - k {
            let gram = &text1[i..i + k];
            set1.insert(self.hash(gram));
        }

        // 提取text2的所有k-gram哈希
        for i in 0..=text2.len() - k {
            let gram = &text2[i..i + k];
            set2.insert(self.hash(gram));
        }

        // 计算Jaccard相似度
        let intersection: std::collections::HashSet<_> = set1.intersection(&set2).collect();
        let union: std::collections::HashSet<_> = set1.union(&set2).collect();

        if union.is_empty() {
            0.0
        } else {
            intersection.len() as f64 / union.len() as f64
        }
    }
}

impl Default for RabinKarp {
    fn default() -> Self {
        Self::new()
    }
}

/// 二维Rabin-Karp（用于图像匹配等）
pub struct RabinKarp2D {
    base_row: u64,
    base_col: u64,
    modulus: u64,
}

impl RabinKarp2D {
    pub fn new() -> Self {
        RabinKarp2D {
            base_row: 256,
            base_col: 911,
            modulus: DEFAULT_MOD,
        }
    }

    /// 在二维矩阵中搜索模式
    ///
    /// # 参数
    /// - `matrix`: 二维文本矩阵
    /// - `pattern`: 二维模式矩阵
    ///
    /// # 返回值
    /// 所有匹配的左上角坐标 (row, col)
    pub fn search<T: Eq + std::hash::Hash>(&self, matrix: &[Vec<T>], pattern: &[Vec<T>]) -> Vec<(usize, usize)>
    where
        T: Clone,
    {
        if pattern.is_empty() || pattern[0].is_empty() {
            return Vec::new();
        }

        let rows = matrix.len();
        let cols = matrix[0].len();
        let pat_rows = pattern.len();
        let pat_cols = pattern[0].len();

        if rows < pat_rows || cols < pat_cols {
            return Vec::new();
        }

        // 简化版：使用字符串表示进行匹配
        // 实际应用中可以使用双重滚动哈希
        let mut matches = Vec::new();

        for r in 0..=rows - pat_rows {
            for c in 0..=cols - pat_cols {
                if Self::match_at(matrix, pattern, r, c) {
                    matches.push((r, c));
                }
            }
        }

        matches
    }

    fn match_at<T: Eq>(matrix: &[Vec<T>], pattern: &[Vec<T>], row: usize, col: usize) -> bool {
        for (i, pat_row) in pattern.iter().enumerate() {
            for (j, pat_val) in pat_row.iter().enumerate() {
                if matrix[row + i][col + j] != *pat_val {
                    return false;
                }
            }
        }
        true
    }
}

impl Default for RabinKarp2D {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_search() {
        let rk = RabinKarp::new();
        let text = "hello world";
        let pattern = "world";
        
        assert_eq!(rk.search(text, pattern), vec![6]);
    }

    #[test]
    fn test_multiple_matches() {
        let rk = RabinKarp::new();
        let text = "abababab";
        let pattern = "aba";
        
        assert_eq!(rk.search(text, pattern), vec![0, 2, 4]);
    }

    #[test]
    fn test_no_match() {
        let rk = RabinKarp::new();
        let text = "hello world";
        let pattern = "xyz";
        
        assert!(rk.search(text, pattern).is_empty());
    }

    #[test]
    fn test_empty_pattern() {
        let rk = RabinKarp::new();
        let text = "hello";
        
        assert!(rk.search(text, "").is_empty());
    }

    #[test]
    fn test_pattern_longer_than_text() {
        let rk = RabinKarp::new();
        let text = "hi";
        let pattern = "hello";
        
        assert!(rk.search(text, pattern).is_empty());
    }

    #[test]
    fn test_overlapping_matches() {
        let rk = RabinKarp::new();
        let text = "aaaaa";
        let pattern = "aa";
        
        assert_eq!(rk.search(text, pattern), vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_multiple_patterns() {
        let rk = RabinKarp::new();
        let text = "the quick brown fox jumps over the lazy dog";
        let patterns = vec!["quick", "fox", "lazy", "cat"];
        
        let results = rk.search_multiple(text, &patterns);
        
        // quick at 4, fox at 16, lazy at 35
        assert!(results.contains(&(0, 4)));
        assert!(results.contains(&(1, 16)));
        assert!(results.contains(&(2, 35)));
        assert!(!results.iter().any(|&(idx, _)| idx == 3)); // cat not found
    }

    #[test]
    fn test_search_any() {
        let rk = RabinKarp::new();
        let text = "hello world";
        let patterns = vec!["xyz", "world", "abc"];
        
        let result = rk.search_any(text, &patterns);
        assert_eq!(result, Some((1, 6)));
    }

    #[test]
    fn test_similarity() {
        let rk = RabinKarp::new();
        
        // 完全相同的文本
        assert_eq!(rk.similarity("hello world", "hello world", 3), 1.0);
        
        // 完全不同的文本
        assert_eq!(rk.similarity("abc", "xyz", 2), 0.0);
        
        // 部分相似
        let sim = rk.similarity("hello world foo", "hello world bar", 3);
        assert!(sim > 0.0 && sim < 1.0);
    }

    #[test]
    fn test_2d_search() {
        let rk2d = RabinKarp2D::new();
        
        let matrix = vec![
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![9, 10, 11, 12],
            vec![13, 14, 15, 16],
        ];
        
        let pattern = vec![
            vec![6, 7],
            vec![10, 11],
        ];
        
        let matches = rk2d.search(&matrix, &pattern);
        assert_eq!(matches, vec![(1, 1)]);
    }

    #[test]
    fn test_unicode() {
        let rk = RabinKarp::new();
        let text = "你好世界，你好Rust";
        let pattern = "你好";
        
        // 注意：这里匹配字节位置
        let matches = rk.search(text, pattern);
        assert!(!matches.is_empty());
    }

    #[test]
    fn test_large_text() {
        let rk = RabinKarp::new();
        let pattern = "pattern";
        let text = "a".repeat(10000) + pattern + &"b".repeat(10000);
        
        let matches = rk.search(&text, pattern);
        assert_eq!(matches, vec![10000]);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn plagiarism_detection_example() {
        println!("\n=== Plagiarism Detection Example ===");
        
        let rk = RabinKarp::new();
        
        let original = "The quick brown fox jumps over the lazy dog. \
                       This is a sample text for testing plagiarism detection.";
        
        let suspicious1 = "The quick brown fox jumps over the lazy dog. \
                          This text has been copied exactly.";
        
        let suspicious2 = "Completely different content here. \
                          Nothing matches the original text at all.";
        
        let sim1 = rk.similarity(original, suspicious1, 10);
        let sim2 = rk.similarity(original, suspicious2, 10);
        
        println!("Similarity with suspicious1: {:.2}%", sim1 * 100.0);
        println!("Similarity with suspicious2: {:.2}%", sim2 * 100.0);
        
        // 设置阈值检测抄袭
        let threshold = 0.3;
        println!("\nPlagiarism detected in suspicious1: {}", sim1 > threshold);
        println!("Plagiarism detected in suspicious2: {}", sim2 > threshold);
    }

    #[test]
    fn text_search_engine_example() {
        println!("\n=== Text Search Engine Example ===");
        
        let rk = RabinKarp::new();
        
        let documents = vec![
            "Rust is a systems programming language that runs blazingly fast",
            "Python is great for data science and machine learning",
            "Rust provides memory safety without garbage collection",
            "JavaScript is the language of the web",
        ];
        
        let keywords = vec!["Rust", "language", "fast"];
        
        for (idx, doc) in documents.iter().enumerate() {
            let matches = rk.search_multiple(doc, &keywords);
            println!("Document {}: found {} keyword matches", idx, matches.len());
            for (kw_idx, pos) in matches {
                println!("  - '{}' at position {}", keywords[kw_idx], pos);
            }
        }
    }

    #[test]
    fn dna_sequence_example() {
        println!("\n=== DNA Sequence Analysis Example ===");
        
        let rk = RabinKarp::with_params(4, 1_000_000_007); // DNA只有4种碱基
        
        let dna = "ATCGATCGATCGATCGATCGATCGATCGATCGATCGATCGATCG";
        let pattern = "ATCGATCG";
        
        let matches = rk.search(dna, pattern);
        println!("Pattern '{}' found at positions: {:?}", pattern, matches);
        
        // 查找特定基因序列
        let genes = vec!["ATCGATCG", "GCTAGCTA", "TATATATA"];
        let gene_matches = rk.search_multiple(dna, &genes);
        println!("Gene matches: {:?}", gene_matches);
    }
}
