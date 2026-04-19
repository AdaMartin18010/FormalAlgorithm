//! KMP (Knuth-Morris-Pratt) 字符串匹配算法实现
//!
//! KMP 算法是一种线性时间复杂度的字符串匹配算法，
//! 由 Donald Knuth、Vaughan Pratt 和 James Morris 于 1977 年联合发表。
//!
//! 对标: CLRS 4th Ed. Chapter 32（String Matching）；MIT 6.006 / Stanford CS161 核心教学内容。
//!
//! ## 核心思想
//!
//! 朴素字符串匹配在失配时，文本指针回退到模式开始位置的下一个字符，时间复杂度 O((n-m+1)m)。
//! KMP 的关键洞察：**利用已匹配的信息，避免文本指针回退**。
//!
//! 通过预处理模式串，构建 **前缀函数 (Prefix Function / Failure Function)** π，
//! 在失配时，模式串根据 π 滑动到合适位置继续比较。
//!
//! ## 前缀函数定义
//!
//! π[q] = 模式串 P[0..q] 的最长相等真前缀与真后缀的长度
//!
//! 例：P = "ababaca"
//! - π[0] = 0 ("a")
//! - π[1] = 0 ("ab")
//! - π[2] = 1 ("aba"，前缀"a"=后缀"a")
//! - π[3] = 2 ("abab"，前缀"ab"=后缀"ab")
//! - π[4] = 3 ("ababa"，前缀"aba"=后缀"aba")
//! - π[5] = 0 ("ababac")
//! - π[6] = 1 ("ababaca"，前缀"a"=后缀"a")
//!
//! ## 复杂度分析
//!
//! - **预处理**: O(m) —— 计算前缀函数
//! - **匹配**: O(n) —— 文本串线性扫描
//! - **总时间**: O(n + m)
//! - **空间**: O(m) —— 存储前缀函数
//!
//! ## 与项目其他字符串算法的关系
//!
//! | 算法 | 时间复杂度 | 适用场景 |
//! |------|----------|---------|
//! | 朴素匹配 | O(nm) | 教学、极短模式 |
//! | **KMP** | **O(n+m)** | **通用单模式匹配** |
//! | Rabin-Karp | O(n+m) 平均 | 多模式匹配、二维匹配 |
//! | Z-Algorithm | O(n+m) | 前缀匹配、字符串周期性分析 |
//! | Boyer-Moore | O(nm) 最坏，亚线性平均 | 长字母表、长模式 |
//! | AC 自动机 | O(n + m + z) | 多模式匹配 |

/// KMP 字符串匹配
///
/// 在文本 `text` 中查找模式 `pattern` 的所有出现位置。
/// 返回模式在文本中每次出现的起始索引列表。
///
/// # 参数
///
/// * `text` - 文本串
/// * `pattern` - 模式串
///
/// # 返回值
///
/// 模式出现的所有起始位置索引（0-based）
///
/// # 示例
///
/// ```
/// use formal_algorithms::kmp::kmp_search;
///
/// let text = "ababababcabab";
/// let pattern = "abab";
/// let matches = kmp_search(text, pattern);
/// assert_eq!(matches, vec![0, 2, 4]);
/// ```
///
/// # 复杂度
///
/// - 时间：O(n + m)，n = |text|，m = |pattern|
/// - 空间：O(m)
pub fn kmp_search(text: &str, pattern: &str) -> Vec<usize> {
    if pattern.is_empty() || text.len() < pattern.len() {
        return vec![];
    }

    let text_bytes = text.as_bytes();
    let pattern_bytes = pattern.as_bytes();
    let n = text_bytes.len();
    let m = pattern_bytes.len();

    let pi = compute_prefix_function(pattern_bytes);

    let mut matches = Vec::new();
    let mut q = 0; // 当前已匹配的模式串长度

    for i in 0..n {
        // 当失配时，利用前缀函数回退
        while q > 0 && (q >= m || text_bytes[i] != pattern_bytes[q]) {
            q = pi[q - 1];
        }
        if text_bytes[i] == pattern_bytes[q] {
            q += 1;
        }
        if q == m {
            matches.push(i + 1 - m);
            q = pi[q - 1]; // 继续查找下一个匹配
        }
    }

    matches
}

/// 计算前缀函数 (Prefix Function / π 函数)
///
/// π[i] = pattern[0..=i] 的最长相等真前缀与真后缀的长度
///
/// # 示例
///
/// ```
/// use formal_algorithms::kmp::compute_prefix_function;
///
/// let pi = compute_prefix_function(b"ababaca");
/// assert_eq!(pi, vec![0, 0, 1, 2, 3, 0, 1]);
/// ```
///
/// # 复杂度
///
/// - 时间：O(m)
/// - 空间：O(m)
pub fn compute_prefix_function(pattern: &[u8]) -> Vec<usize> {
    let m = pattern.len();
    if m == 0 {
        return vec![];
    }

    let mut pi = vec![0; m];
    let mut k = 0; // 当前最长相等前缀后缀长度

    for q in 1..m {
        while k > 0 && pattern[k] != pattern[q] {
            k = pi[k - 1];
        }
        if pattern[k] == pattern[q] {
            k += 1;
        }
        pi[q] = k;
    }

    pi
}

/// KMP 匹配器（流式接口）
///
/// 支持逐步输入文本字符，实时输出匹配位置。
/// 适用于文本流场景（如网络数据包、日志流）。
///
/// # 示例
///
/// ```
/// use formal_algorithms::kmp::KmpMatcher;
///
/// let mut matcher = KmpMatcher::new("abc");
/// let chars: Vec<char> = "xabcyabcz".chars().collect();
/// let mut matches = Vec::new();
/// for (i, ch) in chars.iter().enumerate() {
///     if matcher.feed(*ch, i) {
///         matches.push(i + 1 - matcher.pattern_len());
///     }
/// }
/// assert_eq!(matches, vec![1, 5]);
/// ```
pub struct KmpMatcher {
    pattern: Vec<u8>,
    pi: Vec<usize>,
    state: usize,
}

impl KmpMatcher {
    /// 创建新的 KMP 匹配器
    pub fn new(pattern: &str) -> Self {
        let pattern_bytes = pattern.as_bytes().to_vec();
        let pi = compute_prefix_function(&pattern_bytes);
        KmpMatcher {
            pattern: pattern_bytes,
            pi,
            state: 0,
        }
    }

    /// 输入一个字符，返回是否完成一次匹配
    pub fn feed(&mut self, ch: char, _index: usize) -> bool {
        let ch_byte = ch as u8;
        let m = self.pattern.len();

        while self.state > 0 && (self.state >= m || self.pattern[self.state] != ch_byte) {
            self.state = self.pi[self.state - 1];
        }
        if self.pattern[self.state] == ch_byte {
            self.state += 1;
        }
        if self.state == m {
            self.state = self.pi[self.state - 1];
            true
        } else {
            false
        }
    }

    /// 返回模式串长度
    pub fn pattern_len(&self) -> usize {
        self.pattern.len()
    }

    /// 重置匹配状态
    pub fn reset(&mut self) {
        self.state = 0;
    }
}

/// 判断字符串是否为周期串，返回最小周期长度
///
/// 利用前缀函数性质：若 n % (n - π[n-1]) == 0，则字符串有周期 n - π[n-1]。
///
/// # 示例
///
/// ```
/// use formal_algorithms::kmp::smallest_period;
///
/// assert_eq!(smallest_period("abcabcabc"), Some(3)); // "abc"
/// assert_eq!(smallest_period("abcd"), None);
/// assert_eq!(smallest_period("aaaa"), Some(1));
/// ```
pub fn smallest_period(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n == 0 {
        return None;
    }

    let pi = compute_prefix_function(bytes);
    let period = n - pi[n - 1];

    if n % period == 0 && period < n {
        Some(period)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prefix_function() {
        assert_eq!(compute_prefix_function(b"ababaca"), vec![0, 0, 1, 2, 3, 0, 1]);
        assert_eq!(compute_prefix_function(b"aaaa"), vec![0, 1, 2, 3]);
        assert_eq!(compute_prefix_function(b"abcd"), vec![0, 0, 0, 0]);
        assert_eq!(compute_prefix_function(b"abacabadabacabae"), vec![0, 0, 1, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 0]);
    }

    #[test]
    fn test_kmp_basic() {
        assert_eq!(kmp_search("ababababcabab", "abab"), vec![0, 2, 4, 9]);
        assert_eq!(kmp_search("hello world", "world"), vec![6]);
        assert_eq!(kmp_search("hello world", "xyz"), Vec::<usize>::new());
    }

    #[test]
    fn test_kmp_overlapping() {
        assert_eq!(kmp_search("aaaaa", "aa"), vec![0, 1, 2, 3]);
        assert_eq!(kmp_search("abcabcabc", "abcabc"), vec![0, 3]);
    }

    #[test]
    fn test_kmp_empty() {
        assert_eq!(kmp_search("", "abc"), Vec::<usize>::new());
        assert_eq!(kmp_search("abc", ""), Vec::<usize>::new());
    }

    #[test]
    fn test_kmp_single_char() {
        assert_eq!(kmp_search("aaaaa", "a"), vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_kmp_long() {
        let text = "a".repeat(100000) + "b";
        let pattern = "a".repeat(1000) + "b";
        let matches = kmp_search(&text, &pattern);
        assert_eq!(matches, vec![99000]);
    }

    #[test]
    fn test_smallest_period() {
        assert_eq!(smallest_period("abcabcabc"), Some(3));
        assert_eq!(smallest_period("abcd"), None);
        assert_eq!(smallest_period("aaaa"), Some(1));
        assert_eq!(smallest_period("ababab"), Some(2));
    }

    #[test]
    fn test_streaming_matcher() {
        let mut matcher = KmpMatcher::new("abc");
        let text = "xabcyabcz";
        let mut matches = Vec::new();
        for (i, ch) in text.chars().enumerate() {
            if matcher.feed(ch, i) {
                matches.push(i + 1 - matcher.pattern_len());
            }
        }
        assert_eq!(matches, vec![1, 5]);
    }
}
