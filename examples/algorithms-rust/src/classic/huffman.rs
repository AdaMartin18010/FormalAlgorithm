//! Huffman编码实现
//!
//! Huffman编码是一种贪心算法，用于构建最优前缀码，使得编码后的数据长度最短。
//! 通过给高频字符分配短编码、低频字符分配长编码，实现数据压缩。
//!
//! # 算法原理
//! 1. 统计每个字符的出现频率
//! 2. 将每个字符作为叶子节点，频率作为权重
//! 3. 重复合并两个权重最小的节点，直到只剩一棵树
//! 4. 从根到叶子的路径即为字符的编码
//!
//! # 前缀码性质
//! - 没有任何字符的编码是另一个字符编码的前缀
//! - 保证解码的唯一性
//!
//! # 时间复杂度
//! - 构建频率表: O(n)
//! - 构建Huffman树: O(n log n)
//! - 编码/解码: O(m)，其中m是数据长度
//! - 空间: O(k)，k是不同字符数
//!
//! # 应用
//! - 文件压缩（ZIP, gzip）
//! - 图像压缩（JPEG）
//! - 数据传输优化
//! - 密码学

use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter, Result as FmtResult};

/// Huffman树节点
#[derive(Debug, Clone)]
pub enum HuffmanNode {
    /// 内部节点
    Internal {
        weight: usize,
        left: Box<HuffmanNode>,
        right: Box<HuffmanNode>,
    },
    /// 叶子节点
    Leaf {
        char: char,
        weight: usize,
    },
}

impl HuffmanNode {
    /// 获取节点权重
    fn weight(&self) -> usize {
        match self {
            HuffmanNode::Internal { weight, .. } => *weight,
            HuffmanNode::Leaf { weight, .. } => *weight,
        }
    }

    /// 是否为叶子节点
    fn is_leaf(&self) -> bool {
        matches!(self, HuffmanNode::Leaf { .. })
    }

    /// 获取叶子节点的字符
    fn char(&self) -> Option<char> {
        match self {
            HuffmanNode::Leaf { char, .. } => Some(*char),
            _ => None,
        }
    }
}

/// 用于优先队列的包装器
#[derive(Debug, Clone)]
struct NodeWrapper(Box<HuffmanNode>);

impl PartialEq for NodeWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0.weight() == other.0.weight()
    }
}

impl Eq for NodeWrapper {}

impl PartialOrd for NodeWrapper {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 反向排序，使最小权重在堆顶
        other.0.weight().partial_cmp(&self.0.weight())
    }
}

impl Ord for NodeWrapper {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.weight().cmp(&self.0.weight())
    }
}

/// Huffman编码结果
#[derive(Debug, Clone)]
pub struct HuffmanResult {
    /// 编码表：字符 -> 编码
    pub codes: HashMap<char, String>,
    /// 解码表：编码 -> 字符
    pub reverse_codes: HashMap<String, char>,
    /// Huffman树根节点
    pub root: Option<Box<HuffmanNode>>,
    /// 原始数据大小（位）
    pub original_bits: usize,
    /// 压缩后大小（位）
    pub compressed_bits: usize,
    /// 压缩率
    pub compression_ratio: f64,
}

impl Display for HuffmanResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "Huffman Coding Result:")?;
        writeln!(f, "  Codes:")?;
        let mut codes: Vec<_> = self.codes.iter().collect();
        codes.sort_by_key(|(c, _)| *c);
        for (c, code) in codes {
            writeln!(f, "    '{}': {}", c, code)?;
        }
        writeln!(f, "  Original bits: {}", self.original_bits)?;
        writeln!(f, "  Compressed bits: {}", self.compressed_bits)?;
        writeln!(f, "  Compression ratio: {:.2}%", self.compression_ratio * 100.0)?;
        Ok(())
    }
}

/// Huffman编码器
pub struct HuffmanEncoder;

impl HuffmanEncoder {
    /// 创建新的Huffman编码器
    pub fn new() -> Self {
        HuffmanEncoder
    }

    /// 构建Huffman编码
    ///
    /// # 参数
    /// - `text`: 要编码的文本
    ///
    /// # 返回值
    /// 包含编码表、树结构和统计信息的HuffmanResult
    ///
    /// # 示例
    /// ```
    /// let encoder = HuffmanEncoder::new();
    /// let result = encoder.build_codes("hello world");
    /// ```
    pub fn build_codes(&self, text: &str) -> HuffmanResult {
        if text.is_empty() {
            return HuffmanResult {
                codes: HashMap::new(),
                reverse_codes: HashMap::new(),
                root: None,
                original_bits: 0,
                compressed_bits: 0,
                compression_ratio: 0.0,
            };
        }

        // 统计频率
        let freq_map = self.calculate_frequencies(text);
        let total_chars = text.len();

        // 构建Huffman树
        let root = self.build_tree(&freq_map);

        // 生成编码
        let mut codes = HashMap::new();
        if let Some(ref node) = root {
            self.generate_codes(node, String::new(), &mut codes);
        }

        // 构建反向编码表
        let reverse_codes: HashMap<String, char> = codes
            .iter()
            .map(|(&c, code)| (code.clone(), c))
            .collect();

        // 计算压缩统计
        let original_bits = total_chars * 8; // 假设原始使用8位ASCII/UTF-8
        let compressed_bits: usize = freq_map
            .iter()
            .map(|(c, freq)| freq * codes.get(c).map_or(0, |s| s.len()))
            .sum();

        let compression_ratio = if original_bits > 0 {
            1.0 - (compressed_bits as f64 / original_bits as f64)
        } else {
            0.0
        };

        HuffmanResult {
            codes,
            reverse_codes,
            root,
            original_bits,
            compressed_bits,
            compression_ratio,
        }
    }

    /// 计算字符频率
    fn calculate_frequencies(&self, text: &str) -> HashMap<char, usize> {
        let mut freq = HashMap::new();
        for c in text.chars() {
            *freq.entry(c).or_insert(0) += 1;
        }
        freq
    }

    /// 构建Huffman树
    fn build_tree(&self, freq_map: &HashMap<char, usize>) -> Option<Box<HuffmanNode>> {
        if freq_map.is_empty() {
            return None;
        }

        // 创建优先队列
        let mut heap = BinaryHeap::new();
        for (&c, &freq) in freq_map {
            heap.push(NodeWrapper(Box::new(HuffmanNode::Leaf {
                char: c,
                weight: freq,
            })));
        }

        // 合并节点直到只剩一棵树
        while heap.len() > 1 {
            let left = heap.pop().unwrap().0;
            let right = heap.pop().unwrap().0;

            let parent = Box::new(HuffmanNode::Internal {
                weight: left.weight() + right.weight(),
                left,
                right,
            });

            heap.push(NodeWrapper(parent));
        }

        heap.pop().map(|w| w.0)
    }

    /// 递归生成编码
    fn generate_codes(&self, node: &HuffmanNode, prefix: String, codes: &mut HashMap<char, String>) {
        match node {
            HuffmanNode::Leaf { char, .. } => {
                // 叶子节点，保存编码
                let code = if prefix.is_empty() {
                    "0".to_string()
                } else {
                    prefix
                };
                codes.insert(*char, code);
            }
            HuffmanNode::Internal { left, right, .. } => {
                // 内部节点，递归处理左右子树
                self.generate_codes(left, format!("{}0", prefix), codes);
                self.generate_codes(right, format!("{}1", prefix), codes);
            }
        }
    }

    /// 编码文本
    pub fn encode(&self, text: &str, codes: &HashMap<char, String>) -> String {
        text.chars()
            .filter_map(|c| codes.get(&c).cloned())
            .collect()
    }

    /// 解码比特串
    pub fn decode(&self, encoded: &str, root: &HuffmanNode) -> String {
        let mut result = String::new();
        let mut current = root;

        for bit in encoded.chars() {
            match current {
                HuffmanNode::Internal { left, right, .. } => {
                    current = if bit == '0' { left } else { right };
                }
                _ => unreachable!(),
            }

            if let HuffmanNode::Leaf { char, .. } = current {
                result.push(*char);
                current = root;
            }
        }

        result
    }

    /// 使用编码表解码
    pub fn decode_with_codes(&self, encoded: &str, reverse_codes: &HashMap<String, char>) -> String {
        let mut result = String::new();
        let mut current = String::new();

        for bit in encoded.chars() {
            current.push(bit);
            if let Some(&c) = reverse_codes.get(&current) {
                result.push(c);
                current.clear();
            }
        }

        result
    }
}

impl Default for HuffmanEncoder {
    fn default() -> Self {
        Self::new()
    }
}

/// 辅助函数：一次性编码
pub fn huffman_encode(text: &str) -> (String, HuffmanResult) {
    let encoder = HuffmanEncoder::new();
    let result = encoder.build_codes(text);
    let encoded = encoder.encode(text, &result.codes);
    (encoded, result)
}

/// 辅助函数：一次性解码
pub fn huffman_decode(encoded: &str, root: &HuffmanNode) -> String {
    let encoder = HuffmanEncoder::new();
    encoder.decode(encoded, root)
}

/// 计算熵（信息论下限）
pub fn calculate_entropy(text: &str) -> f64 {
    if text.is_empty() {
        return 0.0;
    }

    let mut freq = HashMap::new();
    for c in text.chars() {
        *freq.entry(c).or_insert(0.0) += 1.0;
    }

    let len = text.len() as f64;
    let mut entropy = 0.0;

    for count in freq.values() {
        let p = count / len;
        entropy -= p * p.log2();
    }

    entropy
}

/// 格式化Huffman树
pub fn format_tree(node: &HuffmanNode, prefix: &str, is_left: bool) -> String {
    let mut result = String::new();

    match node {
        HuffmanNode::Leaf { char, weight } => {
            result.push_str(prefix);
            result.push_str(if is_left { "└── " } else { "├── " });
            result.push_str(&format!("'{}' ({})", char, weight));
            result.push('\n');
        }
        HuffmanNode::Internal { weight, left, right } => {
            result.push_str(prefix);
            result.push_str(if is_left { "└── " } else { "├── " });
            result.push_str(&format!("* ({})", weight));
            result.push('\n');

            let new_prefix = if is_left {
                format!("{}", prefix)
            } else {
                format!("{}│   ", prefix)
            };

            result.push_str(&format_tree(right, &new_prefix, false));
            result.push_str(&format_tree(left, &new_prefix, true));
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_encoding() {
        let encoder = HuffmanEncoder::new();
        let text = "hello world";
        let result = encoder.build_codes(text);

        assert!(!result.codes.is_empty());
        assert!(result.root.is_some());
        assert!(result.compression_ratio >= 0.0);
    }

    #[test]
    fn test_encode_decode() {
        let encoder = HuffmanEncoder::new();
        let text = "hello world, this is a test";
        
        let result = encoder.build_codes(text);
        let encoded = encoder.encode(text, &result.codes);
        let decoded = encoder.decode(&encoded, result.root.as_ref().unwrap());

        assert_eq!(decoded, text);
    }

    #[test]
    fn test_single_char() {
        let encoder = HuffmanEncoder::new();
        let text = "aaaaa";
        
        let result = encoder.build_codes(text);
        assert_eq!(result.codes.len(), 1);
        
        // 单个字符应该编码为"0"
        let code = result.codes.get(&'a').unwrap();
        assert_eq!(code, "0");
    }

    #[test]
    fn test_empty_string() {
        let encoder = HuffmanEncoder::new();
        let result = encoder.build_codes("");
        
        assert!(result.codes.is_empty());
        assert!(result.root.is_none());
    }

    #[test]
    fn test_prefix_property() {
        let encoder = HuffmanEncoder::new();
        let text = "abracadabra";
        
        let result = encoder.build_codes(text);
        let codes: Vec<_> = result.codes.values().collect();

        // 验证前缀码性质：没有任何编码是另一个编码的前缀
        for i in 0..codes.len() {
            for j in 0..codes.len() {
                if i != j {
                    assert!(!codes[j].starts_with(codes[i]));
                }
            }
        }
    }

    #[test]
    fn test_decode_with_codes() {
        let encoder = HuffmanEncoder::new();
        let text = "the quick brown fox";
        
        let result = encoder.build_codes(text);
        let encoded = encoder.encode(text, &result.codes);
        let decoded = encoder.decode_with_codes(&encoded, &result.reverse_codes);

        assert_eq!(decoded, text);
    }

    #[test]
    fn test_unicode() {
        let encoder = HuffmanEncoder::new();
        let text = "你好世界，你好Rust";
        
        let result = encoder.build_codes(text);
        let encoded = encoder.encode(text, &result.codes);
        let decoded = encoder.decode(&encoded, result.root.as_ref().unwrap());

        assert_eq!(decoded, text);
    }

    #[test]
    fn test_entropy() {
        // 完全随机的字符串应该有较高的熵
        let text1 = "abcdefghijklmnopqrstuvwxyz";
        let entropy1 = calculate_entropy(text1);
        assert!(entropy1 > 4.0);

        // 重复字符应该有较低的熵
        let text2 = "aaaaaaaaaa";
        let entropy2 = calculate_entropy(text2);
        assert!(entropy2 < 0.5);
    }

    #[test]
    fn test_convenience_functions() {
        let text = "huffman encoding test";
        let (encoded, result) = huffman_encode(text);
        
        assert!(!encoded.is_empty());
        let decoded = huffman_decode(&encoded, result.root.as_ref().unwrap());
        assert_eq!(decoded, text);
    }

    #[test]
    fn test_large_text() {
        let encoder = HuffmanEncoder::new();
        let text = "the quick brown fox jumps over the lazy dog ".repeat(100);
        
        let result = encoder.build_codes(&text);
        let encoded = encoder.encode(&text, &result.codes);
        let decoded = encoder.decode(&encoded, result.root.as_ref().unwrap());

        assert_eq!(decoded, text);
        // 英文文本通常能达到30-50%的压缩率
        assert!(result.compression_ratio > 0.1);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn basic_usage() {
        println!("\n=== Huffman Encoding Basic Usage ===");

        let text = "this is an example of a huffman tree";
        println!("Original text: '{}'", text);
        println!("Original size: {} bytes", text.len());

        let encoder = HuffmanEncoder::new();
        let result = encoder.build_codes(text);

        println!("\n{}", result);

        let encoded = encoder.encode(text, &result.codes);
        println!("Encoded: {}", encoded);
        println!("Encoded length: {} bits", encoded.len());

        let decoded = encoder.decode(&encoded, result.root.as_ref().unwrap());
        println!("Decoded: '{}'", decoded);
        println!("Match: {}", decoded == text);
    }

    #[test]
    fn tree_visualization() {
        println!("\n=== Huffman Tree Visualization ===");

        let text = "aabbcddddeeeee";
        let encoder = HuffmanEncoder::new();
        let result = encoder.build_codes(text);

        if let Some(ref root) = result.root {
            println!("{}", format_tree(root, "", true));
        }

        println!("Character codes:");
        let mut codes: Vec<_> = result.codes.iter().collect();
        codes.sort_by_key(|(_, code)| code.len());
        for (c, code) in codes {
            println!("  '{}': {} ({} bits)", c, code, code.len());
        }
    }

    #[test]
    fn compression_comparison() {
        println!("\n=== Compression Comparison ===");

        let texts = vec![
            "aaaaabbbbbcccccdddddeeeee",
            "the quick brown fox jumps over the lazy dog",
            "Lorem ipsum dolor sit amet, consectetur adipiscing elit.",
        ];

        let encoder = HuffmanEncoder::new();

        for text in texts {
            let result = encoder.build_codes(text);
            let entropy = calculate_entropy(text);
            let theoretical_min = entropy * text.len() as f64;

            println!("\nText: '{}'", &text[..text.len().min(40)]);
            println!("  Length: {} chars", text.len());
            println!("  Original: {} bits", result.original_bits);
            println!("  Compressed: {} bits", result.compressed_bits);
            println!("  Compression ratio: {:.1}%", result.compression_ratio * 100.0);
            println!("  Entropy: {:.2} bits/char", entropy);
            println!("  Theoretical minimum: {:.0} bits", theoretical_min);
        }
    }

    #[test]
    fn file_compression_simulation() {
        println!("\n=== File Compression Simulation ===");

        // 模拟不同类型文件的压缩效果
        let file_types = vec![
            ("Source code", "fn main() { println!(\"Hello\"); }".repeat(50).as_str()),
            ("JSON data", r#"{"name":"test","value":123}"#.repeat(30).as_str()),
            ("Log file", "[INFO] Application started\n".repeat(20).as_str()),
        ];

        let encoder = HuffmanEncoder::new();

        for (file_type, content) in file_types {
            let result = encoder.build_codes(content);
            println!("\n{}:", file_type);
            println!("  Size: {} bytes", content.len());
            println!("  Compressed: {} bytes", (result.compressed_bits + 7) / 8);
            println!("  Savings: {:.1}%", result.compression_ratio * 100.0);
        }
    }
}
