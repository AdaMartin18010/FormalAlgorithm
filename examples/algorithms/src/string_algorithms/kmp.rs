//! KMP算法实现
//! 
//! 时间复杂度: O(n + m)
//! 空间复杂度: O(m)

/// 计算前缀函数 (pi函数)
/// 
/// pi[i] = P[0..i]的最长相等真前缀和真后缀的长度
/// 
/// # 复杂度
/// - 时间: O(m)
/// - 空间: O(m)
pub fn compute_prefix_function(pattern: &[u8]) -> Vec<usize> {
    let m = pattern.len();
    let mut pi = vec![0; m];
    
    // 当前最长前缀后缀长度
    let mut k = 0;
    
    for q in 1..m {
        // 如果不匹配，回退到前一个可能的前缀
        while k > 0 && pattern[k] != pattern[q] {
            k = pi[k - 1];
        }
        
        // 如果匹配，扩展前缀
        if pattern[k] == pattern[q] {
            k += 1;
        }
        
        pi[q] = k;
    }
    
    pi
}

/// KMP字符串匹配
/// 
/// 返回所有匹配的起始位置 (0-indexed)
/// 
/// # 示例
/// ```
/// let text = "abcabdabcabe";
/// let pattern = "abcabe";
/// let matches = kmp_search(text.as_bytes(), pattern.as_bytes());
/// assert_eq!(matches, vec![6]);
/// ```
pub fn kmp_search(text: &[u8], pattern: &[u8]) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    
    if m == 0 || n < m {
        return Vec::new();
    }
    
    let pi = compute_prefix_function(pattern);
    let mut matches = Vec::new();
    
    // 当前匹配长度
    let mut q = 0;
    
    for i in 0..n {
        // 失配时回退
        while q > 0 && (q >= m || pattern[q] != text[i]) {
            q = pi[q - 1];
        }
        
        // 匹配时扩展
        if pattern[q] == text[i] {
            q += 1;
        }
        
        // 完整匹配
        if q == m {
            matches.push(i - m + 1);
            // 继续寻找，回退
            q = pi[q - 1];
        }
    }
    
    matches
}

/// 流式KMP匹配器
/// 
/// 适用于无法一次性加载全部文本的场景
pub struct KmpMatcher {
    pattern: Vec<u8>,
    pi: Vec<usize>,
    state: usize,  // 当前匹配状态
    position: usize,  // 当前位置
}

impl KmpMatcher {
    pub fn new(pattern: &[u8]) -> Self {
        let pi = compute_prefix_function(pattern);
        KmpMatcher {
            pattern: pattern.to_vec(),
            pi,
            state: 0,
            position: 0,
        }
    }
    
    /// 处理下一个字节，返回是否完成匹配
    pub fn feed(&mut self, byte: u8) -> bool {
        // 失配回退
        while self.state > 0 && self.pattern[self.state] != byte {
            self.state = self.pi[self.state - 1];
        }
        
        // 匹配
        if self.pattern[self.state] == byte {
            self.state += 1;
        }
        
        self.position += 1;
        
        // 检查是否完整匹配
        if self.state == self.pattern.len() {
            // 重置状态以寻找后续匹配
            self.state = self.pi[self.state - 1];
            true
        } else {
            false
        }
    }
    
    pub fn position(&self) -> usize {
        self.position
    }
    
    pub fn reset(&mut self) {
        self.state = 0;
        self.position = 0;
    }
}

/// 多模式KMP匹配 (Aho-Corasick简化版)
pub struct MultiPatternMatcher {
    patterns: Vec<Vec<u8>>,
}

impl MultiPatternMatcher {
    pub fn new(patterns: Vec<&str>) -> Self {
        MultiPatternMatcher {
            patterns: patterns.into_iter().map(|s| s.as_bytes().to_vec()).collect(),
        }
    }
    
    /// 查找所有模式的匹配
    pub fn find_all(&self, text: &str) -> Vec<(usize, usize)> {
        // 结果: (位置, 模式索引)
        let mut results = Vec::new();
        
        for (idx, pattern) in self.patterns.iter().enumerate() {
            let matches = kmp_search(text.as_bytes(), pattern);
            for pos in matches {
                results.push((pos, idx));
            }
        }
        
        // 按位置排序
        results.sort_by_key(|&(pos, _)| pos);
        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_prefix_function() {
        let pattern = "ababaca".as_bytes();
        let pi = compute_prefix_function(pattern);
        assert_eq!(pi, vec![0, 0, 1, 2, 3, 0, 1]);
        
        // 解释:
        // a: 无真前缀后缀 [0]
        // ab: 无 [0]
        // aba: "a"是公共前后缀 [1]
        // abab: "ab"是公共前后缀 [2]
        // ababa: "aba"是公共前后缀 [3]
        // ababac: 无 [0]
        // ababaca: "a"是公共前后缀 [1]
    }
    
    #[test]
    fn test_kmp_basic() {
        let text = "abcabdabcabe";
        let pattern = "abcabe";
        let matches = kmp_search(text.as_bytes(), pattern.as_bytes());
        assert_eq!(matches, vec![6]);
    }
    
    #[test]
    fn test_kmp_multiple() {
        let text = "ababababc";
        let pattern = "abab";
        let matches = kmp_search(text.as_bytes(), pattern.as_bytes());
        assert_eq!(matches, vec![0, 2, 4]);
    }
    
    #[test]
    fn test_kmp_no_match() {
        let text = "abcdef";
        let pattern = "xyz";
        let matches = kmp_search(text.as_bytes(), pattern.as_bytes());
        assert!(matches.is_empty());
    }
    
    #[test]
    fn test_kmp_empty() {
        let text = "abc";
        let pattern = "";
        let matches = kmp_search(text.as_bytes(), pattern.as_bytes());
        assert!(matches.is_empty());
    }
    
    #[test]
    fn test_streaming_matcher() {
        let text = "ababababc";
        let pattern = "abab";
        let mut matcher = KmpMatcher::new(pattern.as_bytes());
        
        let mut matches = Vec::new();
        for (i, &byte) in text.as_bytes().iter().enumerate() {
            if matcher.feed(byte) {
                // 匹配结束于位置i，开始于i - pattern.len() + 1
                matches.push(i - pattern.len() + 1);
            }
        }
        
        assert_eq!(matches, vec![0, 2, 4]);
    }
    
    #[test]
    fn test_multi_pattern() {
        let matcher = MultiPatternMatcher::new(vec!["he", "she", "his", "hers"]);
        let text = "ushers";
        let matches = matcher.find_all(text);
        
        // she 在位置1, he 在位置2, ers 无, hers 无
        assert!(matches.contains(&(1, 1)));  // she
        assert!(matches.contains(&(2, 0)));  // he
    }
}
