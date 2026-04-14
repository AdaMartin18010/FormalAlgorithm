//! Aho-Corasick自动机 (AC自动机)
//!
//! AC自动机是一种多模式字符串匹配算法，可以在O(n + m + z)时间内
//! 在文本中同时查找多个模式串，其中n是文本长度，m是所有模式串总长度，
//! z是匹配次数。
//!
//! # 算法复杂度
//! - 构建时间: O(m)，m为所有模式串总长度
//! - 匹配时间: O(n + z)，n为文本长度，z为匹配数
//! - 空间复杂度: O(m × 字符集大小)
//!
//! # 应用场景
//! - 多关键词过滤
//! - 病毒特征码检测
//! - 敏感词检测
//! - DNA序列多模式匹配

use std::collections::{HashMap, VecDeque};

/// AC自动机节点
#[derive(Debug)]
struct Node {
    /// 子节点映射 (字符 -> 节点ID)
    children: HashMap<char, usize>,
    /// 失败指针
    fail: usize,
    /// 输出模式串的ID列表
    output: Vec<usize>,
    /// 节点深度
    depth: usize,
}

impl Node {
    fn new(depth: usize) -> Self {
        Self {
            children: HashMap::new(),
            fail: 0,
            output: Vec::new(),
            depth,
        }
    }
}

/// AC自动机结构体
#[derive(Debug)]
pub struct ACAutomaton {
    /// Trie树的节点列表
    nodes: Vec<Node>,
    /// 模式串列表
    patterns: Vec<String>,
    /// 是否已构建失败指针
    built: bool,
}

impl ACAutomaton {
    /// 创建空的AC自动机
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::ac_automaton::ACAutomaton;
    /// let ac = ACAutomaton::new();
    /// ```
    pub fn new() -> Self {
        let root = Node::new(0);
        Self {
            nodes: vec![root],
            patterns: Vec::new(),
            built: false,
        }
    }

    /// 从模式串列表构建AC自动机
    ///
    /// # 参数
    /// - `patterns`: 模式串列表
    ///
    /// # 返回
    /// - 构建好的AC自动机
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::ac_automaton::ACAutomaton;
    /// let ac = ACAutomaton::from_patterns(&["he", "she", "his", "hers"]);
    /// ```
    pub fn from_patterns(patterns: &[&str]) -> Self {
        let mut ac = Self::new();
        for (id, &pattern) in patterns.iter().enumerate() {
            ac.insert(pattern, id);
        }
        ac.build();
        ac
    }

    /// 插入单个模式串
    ///
    /// # 参数
    /// - `pattern`: 要插入的模式串
    /// - `id`: 模式串的唯一标识
    fn insert(&mut self, pattern: &str, id: usize) {
        let mut node_id = 0; // 从根节点开始

        for ch in pattern.chars() {
            if !self.nodes[node_id].children.contains_key(&ch) {
                let new_node_id = self.nodes.len();
                let depth = self.nodes[node_id].depth + 1;
                self.nodes.push(Node::new(depth));
                self.nodes[node_id].children.insert(ch, new_node_id);
            }
            node_id = *self.nodes[node_id].children.get(&ch).unwrap();
        }

        self.nodes[node_id].output.push(id);
        
        // 确保patterns列表足够长
        if id >= self.patterns.len() {
            self.patterns.resize(id + 1, String::new());
        }
        self.patterns[id] = pattern.to_string();
    }

    /// 构建失败指针
    ///
    /// 使用BFS遍历Trie树，为每个节点计算失败指针
    /// 时间复杂度: O(总节点数 × 字符集大小)
    fn build(&mut self) {
        if self.built {
            return;
        }

        let mut queue = VecDeque::new();

        // 第一层节点的失败指针指向根节点
        for (&ch, &node_id) in &self.nodes[0].children.clone() {
            queue.push_back((ch, node_id));
        }

        while let Some((_ch, node_id)) = queue.pop_front() {
            // 设置子节点的失败指针
            for (&next_ch, &next_node_id) in &self.nodes[node_id].children.clone() {
                queue.push_back((next_ch, next_node_id));

                // 计算next_node_id的失败指针
                let mut fail = self.nodes[node_id].fail;
                
                // 沿着失败指针链查找可以匹配next_ch的节点
                while fail != 0 && !self.nodes[fail].children.contains_key(&next_ch) {
                    fail = self.nodes[fail].fail;
                }

                // 设置失败指针
                if let Some(&fail_child) = self.nodes[fail].children.get(&next_ch) {
                    if fail_child != next_node_id {
                        self.nodes[next_node_id].fail = fail_child;
                        // 合并输出
                        let output_to_add: Vec<usize> = self.nodes[fail_child].output.clone();
                        self.nodes[next_node_id].output.extend(output_to_add);
                    }
                } else {
                    self.nodes[next_node_id].fail = 0;
                }
            }
        }

        self.built = true;
    }

    /// 在文本中搜索所有模式串
    ///
    /// # 参数
    /// - `text`: 待搜索的文本
    ///
    /// # 返回
    /// - 匹配结果列表，每个元素为 `(模式串ID, 模式串, 结束位置)`
    ///
    /// # 复杂度
    /// - 时间复杂度: O(n + z)，n为文本长度，z为匹配数
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::ac_automaton::ACAutomaton;
    /// let ac = ACAutomaton::from_patterns(&["he", "she", "his", "hers"]);
    /// let matches = ac.search("ushers");
    /// ```
    pub fn search(&self, text: &str) -> Vec<(usize, String, usize)> {
        if !self.built {
            panic!("AC automaton not built. Use from_patterns() or call build() first.");
        }

        let mut result = Vec::new();
        let mut node_id = 0;
        let chars: Vec<char> = text.chars().collect();

        for (i, &ch) in chars.iter().enumerate() {
            // 沿着失败指针查找匹配的转移
            while node_id != 0 && !self.nodes[node_id].children.contains_key(&ch) {
                node_id = self.nodes[node_id].fail;
            }

            // 尝试转移
            if let Some(&next_node) = self.nodes[node_id].children.get(&ch) {
                node_id = next_node;
            }

            // 收集匹配结果
            for &pattern_id in &self.nodes[node_id].output {
                let pattern = &self.patterns[pattern_id];
                let end_pos = i + 1;
                result.push((pattern_id, pattern.clone(), end_pos));
            }
        }

        result
    }

    /// 查找文本中所有匹配的位置
    ///
    /// 返回每个匹配的模式串在文本中的起始位置
    ///
    /// # 返回
    /// - `(模式串, 起始位置)` 的列表
    pub fn find_positions(&self, text: &str) -> Vec<(String, usize)> {
        let matches = self.search(text);
        matches
            .into_iter()
            .map(|(_id, pattern, end_pos)| {
                let start_pos = end_pos - pattern.len();
                (pattern, start_pos)
            })
            .collect()
    }

    /// 统计每个模式串的出现次数
    ///
    /// # 返回
    /// - `(模式串, 出现次数)` 的列表
    pub fn count_occurrences(&self, text: &str) -> Vec<(String, usize)> {
        let matches = self.search(text);
        let mut counts: HashMap<String, usize> = HashMap::new();
        
        for (_, pattern, _) in matches {
            *counts.entry(pattern).or_insert(0) += 1;
        }

        counts.into_iter().collect()
    }

    /// 检查文本中是否包含任何模式串
    ///
    /// 如果有任何一个模式串匹配，立即返回true
    /// 比search更高效，因为可以提前终止
    pub fn contains_any(&self, text: &str) -> bool {
        if !self.built {
            panic!("AC automaton not built.");
        }

        let mut node_id = 0;

        for ch in text.chars() {
            while node_id != 0 && !self.nodes[node_id].children.contains_key(&ch) {
                node_id = self.nodes[node_id].fail;
            }

            if let Some(&next_node) = self.nodes[node_id].children.get(&ch) {
                node_id = next_node;
            }

            // 如果当前节点有输出，说明有匹配
            if !self.nodes[node_id].output.is_empty() {
                return true;
            }
        }

        false
    }

    /// 获取模式串数量
    pub fn pattern_count(&self) -> usize {
        self.patterns.len()
    }

    /// 获取Trie树节点数量
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

impl Default for ACAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_search() {
        let ac = ACAutomaton::from_patterns(&["he", "she", "his", "hers"]);
        let matches = ac.search("ushers");
        
        // "she"在位置3结束，"he"在位置3结束，"hers"在位置6结束
        assert_eq!(matches.len(), 3);
        
        let patterns: Vec<String> = matches.iter().map(|(_, p, _)| p.clone()).collect();
        assert!(patterns.contains(&"she".to_string()));
        assert!(patterns.contains(&"he".to_string()));
        assert!(patterns.contains(&"hers".to_string()));
    }

    #[test]
    fn test_overlapping_patterns() {
        let ac = ACAutomaton::from_patterns(&["a", "ab", "abc", "abcd"]);
        let matches = ac.search("abcd");
        
        // "a"在位置1, "ab"在位置2, "abc"在位置3, "abcd"在位置4
        // 再加上"a"在位置2, "ab"在位置3, "abc"在位置4
        // "a"在位置3, "ab"在位置4
        // "a"在位置4
        assert!(matches.len() >= 4);
        
        let patterns: Vec<String> = matches.iter().map(|(_, p, _)| p.clone()).collect();
        assert!(patterns.contains(&"a".to_string()));
        assert!(patterns.contains(&"ab".to_string()));
        assert!(patterns.contains(&"abc".to_string()));
        assert!(patterns.contains(&"abcd".to_string()));
    }

    #[test]
    fn test_find_positions() {
        let ac = ACAutomaton::from_patterns(&["he", "she"]);
        let positions = ac.find_positions("shehe");
        
        // "she"在位置0开始，"he"在位置1开始，"he"在位置3开始
        let she_positions: Vec<usize> = positions
            .iter()
            .filter(|(p, _)| p == "she")
            .map(|(_, pos)| *pos)
            .collect();
        let he_positions: Vec<usize> = positions
            .iter()
            .filter(|(p, _)| p == "he")
            .map(|(_, pos)| *pos)
            .collect();
        
        assert!(she_positions.contains(&0));
        assert!(he_positions.contains(&1));
        assert!(he_positions.contains(&3));
    }

    #[test]
    fn test_count_occurrences() {
        let ac = ACAutomaton::from_patterns(&["a", "ab", "b"]);
        let counts = ac.count_occurrences("abab");
        
        let count_map: HashMap<String, usize> = counts.into_iter().collect();
        assert_eq!(count_map.get("a"), Some(&2)); // "a"在位置0和2
        assert_eq!(count_map.get("ab"), Some(&2)); // "ab"在位置0和2
        assert_eq!(count_map.get("b"), Some(&2)); // "b"在位置1和3
    }

    #[test]
    fn test_contains_any() {
        let ac = ACAutomaton::from_patterns(&["bad", "word"]);
        
        assert!(ac.contains_any("this is a bad example"));
        assert!(ac.contains_any("badword"));
        assert!(!ac.contains_any("good example"));
    }

    #[test]
    fn test_no_match() {
        let ac = ACAutomaton::from_patterns(&["abc", "def"]);
        let matches = ac.search("xyz");
        assert!(matches.is_empty());
    }

    #[test]
    fn test_empty_pattern() {
        let ac = ACAutomaton::from_patterns(&["", "a"]);
        let matches = ac.search("a");
        // 空字符串应该匹配每个位置
        assert!(matches.len() >= 1);
    }

    #[test]
    fn test_chinese_characters() {
        let ac = ACAutomaton::from_patterns(&["中国", "北京", "中国人"]);
        let matches = ac.search("我是中国人，来自北京");
        
        let patterns: Vec<String> = matches.iter().map(|(_, p, _)| p.clone()).collect();
        assert!(patterns.contains(&"中国".to_string()));
        assert!(patterns.contains(&"北京".to_string()));
        assert!(patterns.contains(&"中国人".to_string()));
    }

    #[test]
    fn test_single_character_patterns() {
        let ac = ACAutomaton::from_patterns(&["a", "b", "c"]);
        let matches = ac.search("abcabc");
        
        assert_eq!(matches.len(), 6); // 每个字符都匹配
    }

    #[test]
    fn test_long_text_performance() {
        let patterns: Vec<String> = (0..100).map(|i| format!("pattern{}", i)).collect();
        let pattern_refs: Vec<&str> = patterns.iter().map(|s| s.as_str()).collect();
        let ac = ACAutomaton::from_patterns(&pattern_refs);
        
        let text = "pattern50".repeat(1000);
        let matches = ac.search(&text);
        
        assert!(!matches.is_empty());
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 基本用法 - 多模式匹配
    pub fn example_basic() {
        println!("=== AC自动机基本用法 ===");
        
        let patterns = &["he", "she", "his", "hers"];
        let ac = ACAutomaton::from_patterns(patterns);
        
        let text = "ushers";
        let matches = ac.search(text);
        
        println!("文本: {}", text);
        println!("模式串: {:?}", patterns);
        println!("匹配结果:");
        for (id, pattern, end_pos) in matches {
            let start_pos = end_pos - pattern.len();
            println!("  模式 '{}' (ID={}) 在位置 [{}..{}] 匹配", 
                pattern, id, start_pos, end_pos);
        }
    }

    /// 示例2: 敏感词过滤
    pub fn example_sensitive_word_filter() {
        println!("\n=== 敏感词过滤示例 ===");
        
        let sensitive_words = &["bad", "worse", "worst", "inappropriate"];
        let ac = ACAutomaton::from_patterns(sensitive_words);
        
        let texts = vec![
            "This is a good example",
            "This is bad behavior",
            "The worst case scenario",
        ];
        
        for text in texts {
            if ac.contains_any(text) {
                let matches = ac.find_positions(text);
                println!("文本 '{}' 包含敏感词:", text);
                for (word, pos) in matches {
                    println!("  发现 '{}' 在位置 {}", word, pos);
                }
            } else {
                println!("文本 '{}' 通过检查", text);
            }
        }
    }

    /// 示例3: 统计词频
    pub fn example_word_frequency() {
        println!("\n=== 词频统计示例 ===");
        
        let keywords = &["rust", "programming", "language", "system"];
        let ac = ACAutomaton::from_patterns(keywords);
        
        let article = "Rust is a systems programming language. \
            Rust programming is fun. \
            System programming requires a good language like Rust.";
        
        let counts = ac.count_occurrences(article.to_lowercase().as_str());
        
        println!("文章关键词统计:");
        for (word, count) in counts {
            println!("  '{}': {} 次", word, count);
        }
    }
}
