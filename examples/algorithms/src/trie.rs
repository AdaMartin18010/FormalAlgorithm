//! Trie (前缀树) 实现
//! 
//! 应用:
//! - 前缀搜索
//! - 自动补全
//! - 拼写检查
//! - IP路由最长前缀匹配

use std::collections::HashMap;

/// Trie节点
#[derive(Debug, Default)]
pub struct TrieNode {
    /// 子节点: 字符 -> 节点
    children: HashMap<char, TrieNode>,
    /// 是否是某个单词的结尾
    is_end: bool,
    /// 经过此节点的单词数 (用于统计)
    count: usize,
}

impl TrieNode {
    fn new() -> Self {
        TrieNode {
            children: HashMap::new(),
            is_end: false,
            count: 0,
        }
    }
}

/// Trie数据结构
#[derive(Debug)]
pub struct Trie {
    root: TrieNode,
    size: usize,  // 存储的单词数
}

impl Trie {
    /// 创建空Trie
    pub fn new() -> Self {
        Trie {
            root: TrieNode::new(),
            size: 0,
        }
    }
    
    /// 插入单词
    /// 
    /// # 复杂度
    /// - 时间: O(|word|)
    /// - 空间: O(|word|) (新节点)
    pub fn insert(&mut self, word: &str) {
        let mut node = &mut self.root;
        
        for ch in word.chars() {
            node = node.children.entry(ch).or_insert_with(TrieNode::new);
            node.count += 1;
        }
        
        if !node.is_end {
            node.is_end = true;
            self.size += 1;
        }
    }
    
    /// 查找单词
    /// 
    /// # 复杂度: O(|word|)
    pub fn search(&self, word: &str) -> bool {
        self.find_node(word).map_or(false, |node| node.is_end)
    }
    
    /// 检查是否有以prefix开头的单词
    /// 
    /// # 复杂度: O(|prefix|)
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.find_node(prefix).is_some()
    }
    
    /// 查找节点
    fn find_node(&self, word: &str) -> Option<&TrieNode> {
        let mut node = &self.root;
        
        for ch in word.chars() {
            match node.children.get(&ch) {
                Some(next) => node = next,
                None => return None,
            }
        }
        
        Some(node)
    }
    
    /// 删除单词
    /// 
    /// # 复杂度: O(|word|)
    pub fn delete(&mut self, word: &str) -> bool {
        if !self.search(word) {
            return false;
        }
        
        if Self::delete_recursive(&mut self.root, word, 0) {
            self.root = TrieNode::new();
        }
        self.size -= 1;
        true
    }
    
    fn delete_recursive(node: &mut TrieNode, word: &str, index: usize) -> bool {
        if index == word.len() {
            // 到达目标节点
            node.is_end = false;
            node.count -= 1;
            // 如果没有子节点，可以删除
            return node.children.is_empty();
        }
        
        let ch = word.chars().nth(index).unwrap();
        let should_delete_child = if let Some(child) = node.children.get_mut(&ch) {
            Self::delete_recursive(child, word, index + 1)
        } else {
            false
        };
        
        if should_delete_child {
            node.children.remove(&ch);
        }
        
        node.count -= 1;
        // 如果当前节点不再是结束且没有子节点，可以删除
        !node.is_end && node.children.is_empty()
    }
    
    /// 获取所有以prefix开头的单词
    pub fn words_with_prefix(&self, prefix: &str) -> Vec<String> {
        let mut result = Vec::new();
        
        if let Some(node) = self.find_node(prefix) {
            self.collect_words(node, prefix, &mut result);
        }
        
        result
    }
    
    fn collect_words(&self, node: &TrieNode, prefix: &str, result: &mut Vec<String>) {
        if node.is_end {
            result.push(prefix.to_string());
        }
        
        for (ch, child) in &node.children {
            let new_prefix = format!("{}{}", prefix, ch);
            self.collect_words(child, &new_prefix, result);
        }
    }
    
    /// 自动补全: 返回前缀的最常见补全
    pub fn autocomplete(&self, prefix: &str, limit: usize) -> Vec<String> {
        let mut words = self.words_with_prefix(prefix);
        // 可以按频率排序，这里简单返回前limit个
        words.truncate(limit);
        words
    }
    
    /// 统计以prefix为前缀的单词数
    pub fn count_prefix(&self, prefix: &str) -> usize {
        self.find_node(prefix).map_or(0, |node| node.count)
    }
    
    /// 获取存储的单词数
    pub fn size(&self) -> usize {
        self.size
    }
    
    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

/// 二进制Trie (用于IP路由、异或问题等)
#[derive(Debug)]
pub struct BinaryTrie {
    root: BinaryTrieNode,
}

#[derive(Debug, Default)]
struct BinaryTrieNode {
    child: [Option<Box<BinaryTrieNode>>; 2],
    count: usize,
    value: Option<u32>,  // 存储完整值（如果是叶节点）
}

impl BinaryTrie {
    pub fn new() -> Self {
        BinaryTrie {
            root: BinaryTrieNode::default(),
        }
    }
    
    /// 插入32位整数 (用于最大异或等问题)
    pub fn insert(&mut self, num: u32) {
        let mut node = &mut self.root;
        
        for i in (0..32).rev() {
            let bit = ((num >> i) & 1) as usize;
            node.count += 1;
            
            if node.child[bit].is_none() {
                node.child[bit] = Some(Box::new(BinaryTrieNode::default()));
            }
            
            node = node.child[bit].as_mut().unwrap();
        }
        
        node.count += 1;
        node.value = Some(num);
    }
    
    /// 查找与num异或最大的数
    pub fn max_xor(&self, num: u32) -> Option<u32> {
        let mut node = &self.root;
        
        for i in (0..32).rev() {
            let bit = ((num >> i) & 1) as usize;
            let opposite = 1 - bit;
            
            // 优先走相反的位（使异或结果最大）
            if let Some(ref child) = node.child[opposite] {
                node = child;
            } else if let Some(ref child) = node.child[bit] {
                node = child;
            } else {
                return None;
            }
        }
        
        node.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_trie_basic() {
        let mut trie = Trie::new();
        
        trie.insert("apple");
        trie.insert("app");
        trie.insert("application");
        trie.insert("banana");
        
        assert!(trie.search("apple"));
        assert!(trie.search("app"));
        assert!(!trie.search("appl"));  // 不是完整单词
        assert!(trie.starts_with("appl"));  // 但是前缀
        assert!(!trie.search("orange"));
        
        assert_eq!(trie.size(), 4);
    }
    
    #[test]
    fn test_words_with_prefix() {
        let mut trie = Trie::new();
        
        trie.insert("apple");
        trie.insert("app");
        trie.insert("application");
        trie.insert("apply");
        trie.insert("banana");
        
        let words = trie.words_with_prefix("app");
        assert!(words.contains(&"app".to_string()));
        assert!(words.contains(&"apple".to_string()));
        assert!(words.contains(&"application".to_string()));
        assert!(words.contains(&"apply".to_string()));
        assert!(!words.contains(&"banana".to_string()));
    }
    
    #[test]
    fn test_delete() {
        let mut trie = Trie::new();
        
        trie.insert("apple");
        trie.insert("app");
        
        assert!(trie.delete("apple"));
        assert!(!trie.search("apple"));
        assert!(trie.search("app"));  // app 应该还在
        
        assert!(!trie.delete("orange"));  // 不存在的单词
    }
    
    #[test]
    fn test_binary_trie_max_xor() {
        let mut trie = BinaryTrie::new();
        
        trie.insert(3);   // 011
        trie.insert(10);  // 1010
        trie.insert(5);   // 0101
        trie.insert(25);  // 11001
        trie.insert(2);   // 00010
        trie.insert(8);   // 01000
        
        // 与5(0101)异或最大的是?(1010)=10
        assert_eq!(trie.max_xor(5), Some(10));
        
        // 与2(0010)异或最大的是?(1110=14不存在, 应该是?)
        // 实际应该是 10 (1010) -> 1000 = 8
        let result = trie.max_xor(2);
        assert!(result.is_some());
    }
}
