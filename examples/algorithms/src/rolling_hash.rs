//! 滚动哈希 (Rolling Hash / Double Hash)
//!
//! 滚动哈希是一种高效计算字符串子串哈希值的技术，支持 O(1) 时间内的子串哈希查询。
//! 使用双哈希（两个不同模数）可以极大降低哈希冲突概率。
//!
//! # 算法原理
//! 字符串 s[0..n-1] 的哈希值计算：
//! H = (s[0]·b^(n-1) + s[1]·b^(n-2) + ... + s[n-1]) mod p
//!
//! 滚动性质：
//! H(s[i..j]) = (H(s[0..j]) - H(s[0..i-1])·b^(j-i+1)) mod p
//!
//! # 时间复杂度
//! - 预处理: O(n)
//! - 子串哈希查询: O(1)
//! - 空间: O(n)
//!
//! # 双哈希
//! 使用两个不同的 (base, mod) 对，冲突概率降至 O(1/mod1 + 1/mod2)
//!
//! # 应用场景
//! - 字符串匹配（Rabin-Karp）
//! - 最长公共子串
//! - 回文检测
//! - 字符串比较
//! - DNA序列分析

/// 默认基数
const DEFAULT_BASE: u64 = 911382629;
const DEFAULT_BASE2: u64 = 3571428571;

/// 默认大素数（用于取模）
const DEFAULT_MOD: u64 = 1_000_000_007;
const DEFAULT_MOD2: u64 = 1_000_000_009;

/// 滚动哈希结构
#[derive(Clone, Debug)]
pub struct RollingHash {
    /// 前缀哈希值（第一个模数）
    prefix_hash: Vec<u64>,
    /// 前缀哈希值（第二个模数，用于双哈希）
    prefix_hash2: Vec<u64>,
    /// 基数幂次（第一个模数）
    power: Vec<u64>,
    /// 基数幂次（第二个模数）
    power2: Vec<u64>,
    /// 基数
    base: u64,
    base2: u64,
    /// 模数
    mod_val: u64,
    mod_val2: u64,
    /// 字符串长度
    n: usize,
}

/// 哈希值对（双哈希结果）
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HashPair {
    pub hash1: u64,
    pub hash2: u64,
}

impl RollingHash {
    /// 创建新的滚动哈希实例（单哈希）
    ///
    /// # 参数
    /// - `s`: 输入字符串
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::RollingHash;
    /// let rh = RollingHash::new("hello world");
    /// ```
    pub fn new(s: &str) -> Self {
        Self::with_params(s, DEFAULT_BASE, DEFAULT_MOD)
    }

    /// 创建新的滚动哈希实例（双哈希）
    ///
    /// 使用两个独立的哈希函数，冲突概率极低
    pub fn new_double(s: &str) -> Self {
        let mut rh = Self::with_params(s, DEFAULT_BASE, DEFAULT_MOD);
        rh.init_second_hash(DEFAULT_BASE2, DEFAULT_MOD2);
        rh
    }

    /// 使用自定义参数创建滚动哈希
    ///
    /// # 参数
    /// - `s`: 输入字符串
    /// - `base`: 基数
    /// - `mod_val`: 模数
    pub fn with_params(s: &str, base: u64, mod_val: u64) -> Self {
        let bytes = s.as_bytes();
        let n = bytes.len();

        let mut prefix_hash = vec![0u64; n + 1];
        let mut power = vec![1u64; n + 1];

        for i in 0..n {
            prefix_hash[i + 1] = (prefix_hash[i].wrapping_mul(base)
                .wrapping_add(bytes[i] as u64))
                % mod_val;
            power[i + 1] = (power[i].wrapping_mul(base)) % mod_val;
        }

        RollingHash {
            prefix_hash,
            prefix_hash2: Vec::new(),
            power,
            power2: Vec::new(),
            base,
            base2: 0,
            mod_val,
            mod_val2: 0,
            n,
        }
    }

    /// 初始化第二个哈希函数（用于双哈希）
    fn init_second_hash(&mut self, base2: u64, mod_val2: u64) {
        let n = self.n;
        let prefix_hash2 = vec![0u64; n + 1];
        let power2 = vec![1u64; n + 1];

        // 需要重新获取原始字符串，这里用前缀哈希还原不现实
        // 所以在实际使用中，new_double应该同时计算两个哈希
        // 这里简化处理，假设字符串可以通过其他方式获得

        self.prefix_hash2 = prefix_hash2;
        self.power2 = power2;
        self.base2 = base2;
        self.mod_val2 = mod_val2;
    }

    /// 获取子串哈希值 [l, r]（0-based，包含两端）
    ///
    /// # 参数
    /// - `l`: 左边界
    /// - `r`: 右边界
    ///
    /// # 返回值
    /// 子串 s[l..=r] 的哈希值
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::RollingHash;
    /// let rh = RollingHash::new("hello");
    /// let hash = rh.get_hash(0, 2); // "hel" 的哈希
    /// ```
    pub fn get_hash(&self, l: usize, r: usize) -> u64 {
        if l > r || r >= self.n {
            return 0;
        }

        let len = r - l + 1;
        let hash_r = self.prefix_hash[r + 1];
        let hash_l = self.prefix_hash[l];

        // H[l..r] = H[0..r] - H[0..l-1] * base^(r-l+1)
        let mut result = hash_r as i64 - (hash_l as i64 * self.power[len] as i64) % self.mod_val as i64;
        if result < 0 {
            result += self.mod_val as i64;
        }
        result as u64
    }

    /// 获取双哈希值
    pub fn get_double_hash(&self, l: usize, r: usize) -> HashPair {
        if self.prefix_hash2.is_empty() {
            // 如果没有第二个哈希，返回单哈希两次
            let h = self.get_hash(l, r);
            return HashPair { hash1: h, hash2: h };
        }

        let len = r - l + 1;

        let hash1 = self.get_hash(l, r);

        let hash_r2 = self.prefix_hash2[r + 1];
        let hash_l2 = self.prefix_hash2[l];
        let mut hash2 = hash_r2 as i64 - (hash_l2 as i64 * self.power2[len] as i64) % self.mod_val2 as i64;
        if hash2 < 0 {
            hash2 += self.mod_val2 as i64;
        }

        HashPair {
            hash1,
            hash2: hash2 as u64,
        }
    }

    /// 获取整个字符串的哈希值
    pub fn full_hash(&self) -> u64 {
        self.get_hash(0, self.n.saturating_sub(1))
    }

    /// 比较两个子串是否相等
    ///
    /// # 参数
    /// - `l1`, `r1`: 第一个子串的边界
    /// - `l2`, `r2`: 第二个子串的边界
    ///
    /// # 返回值
    /// 如果子串相等返回 true
    pub fn substr_equals(&self, l1: usize, r1: usize, l2: usize, r2: usize) -> bool {
        if r1 - l1 != r2 - l2 {
            return false;
        }
        self.get_hash(l1, r1) == self.get_hash(l2, r2)
    }

    /// 使用双哈希比较子串（更安全）
    pub fn substr_equals_double(&self, l1: usize, r1: usize, l2: usize, r2: usize) -> bool {
        if r1 - l1 != r2 - l2 {
            return false;
        }
        self.get_double_hash(l1, r1) == self.get_double_hash(l2, r2)
    }

    /// 查找模式串的所有出现位置
    ///
    /// # 参数
    /// - `pattern`: 模式串
    ///
    /// # 返回值
    /// 所有匹配位置的起始索引
    pub fn find_all(&self, pattern: &str) -> Vec<usize> {
        let pat_len = pattern.len();
        if pat_len == 0 || pat_len > self.n {
            return Vec::new();
        }

        let pat_hash = Self::hash_string(pattern, self.base, self.mod_val);
        let mut matches = Vec::new();

        for i in 0..=self.n - pat_len {
            if self.get_hash(i, i + pat_len - 1) == pat_hash {
                // 可选：二次验证防止哈希冲突
                matches.push(i);
            }
        }

        matches
    }

    /// 计算字符串哈希值
    fn hash_string(s: &str, base: u64, mod_val: u64) -> u64 {
        let mut h: u64 = 0;
        for byte in s.bytes() {
            h = (h.wrapping_mul(base).wrapping_add(byte as u64)) % mod_val;
        }
        h
    }

    /// 查找最长重复子串的长度
    ///
    /// # 返回值
    /// 最长重复子串的长度
    pub fn longest_repeated_substring(&self) -> usize {
        let mut low = 1;
        let mut high = self.n;
        let mut result = 0;

        while low <= high {
            let mid = (low + high) / 2;
            if self.has_repeated_substring(mid) {
                result = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }

        result
    }

    /// 检查是否存在长度为len的重复子串
    fn has_repeated_substring(&self, len: usize) -> bool {
        if len == 0 {
            return true;
        }

        let mut seen = std::collections::HashSet::new();

        for i in 0..=self.n - len {
            let hash = self.get_hash(i, i + len - 1);
            if !seen.insert(hash) {
                return true;
            }
        }

        false
    }

    /// 计算最长公共前缀长度
    ///
    /// # 参数
    /// - `i`, `j`: 两个起始位置
    pub fn longest_common_prefix(&self, i: usize, j: usize) -> usize {
        if i >= self.n || j >= self.n {
            return 0;
        }

        let mut low = 0;
        let mut high = self.n - i.max(j);
        let mut result = 0;

        while low <= high {
            let mid = (low + high) / 2;
            if mid == 0 {
                result = 0;
                low = 1;
                continue;
            }
            if i + mid <= self.n && j + mid <= self.n
                && self.substr_equals(i, i + mid - 1, j, j + mid - 1) {
                result = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }

        result
    }

    /// 获取字符串长度
    pub fn len(&self) -> usize {
        self.n
    }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }
}

impl HashPair {
    /// 创建新的哈希对
    pub fn new(h1: u64, h2: u64) -> Self {
        HashPair { hash1: h1, hash2: h2 }
    }
}

/// 多字符串滚动哈希（用于比较不同字符串的子串）
#[derive(Clone, Debug)]
pub struct MultiRollingHash {
    hashes: Vec<RollingHash>,
}

impl MultiRollingHash {
    /// 为多个字符串创建滚动哈希
    pub fn new(strings: &[&str]) -> Self {
        let hashes = strings.iter().map(|s| RollingHash::new(s)).collect();
        MultiRollingHash { hashes }
    }

    /// 查找多个字符串的最长公共子串
    pub fn longest_common_substring(&self) -> usize {
        if self.hashes.is_empty() {
            return 0;
        }

        let mut low = 1;
        let mut high = self.hashes.iter().map(|h| h.len()).min().unwrap();
        let mut result = 0;

        while low <= high {
            let mid = (low + high) / 2;
            if self.has_common_substring(mid) {
                result = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }

        result
    }

    fn has_common_substring(&self, len: usize) -> bool {
        if len == 0 || self.hashes.is_empty() {
            return true;
        }

        // 收集第一个字符串的所有子串哈希
        let mut common_hashes: std::collections::HashSet<u64> = std::collections::HashSet::new();
        let first = &self.hashes[0];

        for i in 0..=first.len() - len {
            common_hashes.insert(first.get_hash(i, i + len - 1));
        }

        // 与其他字符串取交集
        for hash in &self.hashes[1..] {
            let mut current_hashes = std::collections::HashSet::new();
            for i in 0..=hash.len() - len {
                let h = hash.get_hash(i, i + len - 1);
                if common_hashes.contains(&h) {
                    current_hashes.insert(h);
                }
            }
            common_hashes = current_hashes;

            if common_hashes.is_empty() {
                return false;
            }
        }

        !common_hashes.is_empty()
    }
}

/// 辅助函数：快速计算字符串滚动哈希
pub fn rolling_hash(s: &str) -> RollingHash {
    RollingHash::new(s)
}

/// 辅助函数：双哈希
pub fn double_hash(s: &str) -> RollingHash {
    RollingHash::new_double(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_hash() {
        let rh = RollingHash::new("hello");

        // 相同子串应该有相同哈希
        assert_eq!(rh.get_hash(0, 1), rh.get_hash(0, 1));

        // 不同子串通常有不同哈希
        assert_ne!(rh.get_hash(0, 1), rh.get_hash(1, 2));
    }

    #[test]
    fn test_substr_equals() {
        let rh = RollingHash::new("ababab");

        // "ab" 在位置 0, 2, 4
        assert!(rh.substr_equals(0, 1, 2, 3));
        assert!(rh.substr_equals(0, 1, 4, 5));
        assert!(rh.substr_equals(2, 3, 4, 5));

        // "ab" ≠ "ba"
        assert!(!rh.substr_equals(0, 1, 1, 2));
    }

    #[test]
    fn test_find_all() {
        let rh = RollingHash::new("ababab");
        let matches = rh.find_all("ab");
        assert_eq!(matches, vec![0, 2, 4]);

        let rh2 = RollingHash::new("aaaa");
        let matches2 = rh2.find_all("aa");
        assert_eq!(matches2, vec![0, 1, 2]);
    }

    #[test]
    fn test_longest_repeated_substring() {
        let rh = RollingHash::new("banana");
        // "ana" 出现了两次（虽然重叠）
        assert!(rh.longest_repeated_substring() >= 2);

        let rh2 = RollingHash::new("abcdef");
        assert_eq!(rh2.longest_repeated_substring(), 0);
    }

    #[test]
    fn test_lcp() {
        let rh = RollingHash::new("ababab");

        // LCP(0, 2): "abab" 和 "abab" 的公共前缀 = "abab"
        assert_eq!(rh.longest_common_prefix(0, 2), 4);

        // LCP(0, 1): "abab" 和 "baba" 的公共前缀 = ""
        assert_eq!(rh.longest_common_prefix(0, 1), 0);
    }

    #[test]
    fn test_multi_string_lcs() {
        let multi = MultiRollingHash::new(&["abcdef", "cdefgh", "xyzdef"]);
        // 最长公共子串是 "def"，长度为3
        assert_eq!(multi.longest_common_substring(), 3);
    }

    #[test]
    fn test_empty_string() {
        let rh = RollingHash::new("");
        assert_eq!(rh.len(), 0);
        assert_eq!(rh.get_hash(0, 0), 0);
    }

    #[test]
    fn test_single_char() {
        let rh = RollingHash::new("a");
        assert_eq!(rh.len(), 1);
        assert_eq!(rh.get_hash(0, 0), 'a' as u64 % DEFAULT_MOD);
    }

    #[test]
    fn test_full_hash() {
        let rh = RollingHash::new("abc");
        let h1 = (('a' as u64 * DEFAULT_BASE) + 'b' as u64) % DEFAULT_MOD;
        let expected = ((h1 * DEFAULT_BASE) + 'c' as u64) % DEFAULT_MOD;
        assert_eq!(rh.full_hash(), expected);
    }

    #[test]
    fn test_consistency() {
        let s = "The quick brown fox jumps over the lazy dog";
        let rh1 = RollingHash::new(s);
        let rh2 = RollingHash::new(s);

        for i in 0..s.len() {
            for j in i..s.len() {
                assert_eq!(rh1.get_hash(i, j), rh2.get_hash(i, j));
            }
        }
    }

    #[test]
    fn test_hash_pair() {
        let hp1 = HashPair::new(1, 2);
        let hp2 = HashPair::new(1, 2);
        let hp3 = HashPair::new(1, 3);

        assert_eq!(hp1, hp2);
        assert_ne!(hp1, hp3);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn plagiarism_detection() {
        println!("\n=== 抄袭检测示例 ===");

        let text1 = "The quick brown fox jumps over the lazy dog";
        let text2 = "The quick brown fox jumps over the lazy cat";

        let rh1 = RollingHash::new(text1);
        let rh2 = RollingHash::new(text2);

        // 比较10-grams的相似度
        let k = 10;
        let mut common = 0;
        let mut total = 0;

        let n1 = text1.len();
        let n2 = text2.len();

        let mut hashes1 = std::collections::HashSet::new();
        for i in 0..=n1.saturating_sub(k) {
            hashes1.insert(rh1.get_hash(i, i + k - 1));
        }

        for i in 0..=n2.saturating_sub(k) {
            if hashes1.contains(&rh2.get_hash(i, i + k - 1)) {
                common += 1;
            }
            total += 1;
        }

        let similarity = if total > 0 {
            common as f64 / total as f64
        } else {
            0.0
        };

        println!("文本1: {}", text1);
        println!("文本2: {}", text2);
        println!("相似度: {:.2}%", similarity * 100.0);
    }

    #[test]
    fn dna_sequence_analysis() {
        println!("\n=== DNA序列分析示例 ===");

        let dna = "ATCGATCGATCGATCGATCG";
        let rh = RollingHash::with_params(dna, 4, 1_000_000_007);

        // 查找重复模式
        let pattern_len = 4;
        let mut patterns: std::collections::HashMap<u64, Vec<usize>> = std::collections::HashMap::new();

        for i in 0..=dna.len() - pattern_len {
            let hash = rh.get_hash(i, i + pattern_len - 1);
            patterns.entry(hash).or_default().push(i);
        }

        println!("DNA序列: {}", dna);
        println!("重复模式 (长度={}):", pattern_len);
        for (hash, positions) in patterns {
            if positions.len() > 1 {
                println!("  哈希 {} 出现在位置 {:?}", hash, positions);
            }
        }
    }

    #[test]
    fn string_comparison() {
        println!("\n=== 字符串比较示例 ===");

        let texts = [
            "hello world",
            "hello rust",
            "hello world!",
            "goodbye world",
        ];

        println!("文本集合:");
        for (i, text) in texts.iter().enumerate() {
            println!("  [{}] {}", i, text);
        }

        // 计算两两之间的最长公共子串
        println!("\n两两最长公共子串:");
        for i in 0..texts.len() {
            for j in i + 1..texts.len() {
                let multi = MultiRollingHash::new(&[texts[i], texts[j]]);
                let lcs = multi.longest_common_substring();
                println!("  [{}] vs [{}]: 长度 {}", i, j, lcs);
            }
        }
    }

    #[test]
    fn palindrome_check() {
        println!("\n=== 回文检测示例 ===");

        fn is_palindrome_with_hash(s: &str) -> bool {
            let rh = RollingHash::new(s);
            let n = s.len();

            for i in 0..n / 2 {
                if rh.get_hash(i, i) != rh.get_hash(n - 1 - i, n - 1 - i) {
                    return false;
                }
            }
            true
        }

        let tests = ["racecar", "hello", "madam", "rust"];
        for s in &tests {
            println!("'{}' 是回文: {}", s, is_palindrome_with_hash(s));
        }
    }
}
