//! 最优二叉搜索树（Optimal BST）
//!
//! 最优二叉搜索树问题研究如何根据关键字的搜索概率构建平均搜索代价最小的BST。
//! 与标准BST不同，最优BST考虑不同关键字被搜索的频率，将高频关键字放在靠近根的位置。
//!
//! # 问题定义
//! 给定n个有序关键字 k₁ < k₂ < ... < kₙ，以及：
//! - p[i]: 搜索关键字 kᵢ 的概率
//! - q[i]: 搜索值在 (kᵢ, kᵢ₊₁) 区间内的概率（虚拟键）
//!
//! 找到使期望搜索代价最小的BST结构。
//!
//! # 动态规划解法
//! - 状态定义：e[i][j] 表示包含关键字 kᵢ 到 kⱼ 的最优BST的期望搜索代价
//! - 状态转移：e[i][j] = min(e[i][r-1] + e[r+1][j] + w(i,j))
//! - 时间复杂度：O(n³)，可优化到 O(n²)（Knuth优化）
//! - 空间复杂度：O(n²)
//!
//! # 应用场景
//! - 编译器符号表
//! - 数据库索引
//! - 字典/词汇表组织
//! - 文件系统目录结构

use std::fmt::Display;

/// 最优BST节点
#[derive(Debug, Clone)]
pub struct Node<K: Ord + Clone> {
    pub key: K,
    pub left: Option<Box<Node<K>>>,
    pub right: Option<Box<Node<K>>>,
}

impl<K: Ord + Clone> Node<K> {
    fn new(key: K) -> Self {
        Node {
            key,
            left: None,
            right: None,
        }
    }
}

/// 最优BST求解结果
#[derive(Debug, Clone)]
pub struct OptimalBSTResult<K: Ord + Clone> {
    /// 最小期望搜索代价
    pub min_cost: f64,
    /// 最优BST的根节点
    pub root: Option<Box<Node<K>>>,
    /// 根节点选择表
    pub root_table: Vec<Vec<usize>>,
    /// 代价表
    pub cost_table: Vec<Vec<f64>>,
}

/// 最优BST求解器
pub struct OptimalBST<K: Ord + Clone> {
    /// 关键字
    keys: Vec<K>,
    /// 成功搜索概率
    p: Vec<f64>,
    /// 失败搜索概率（虚拟键）
    q: Vec<f64>,
    /// 关键字数量
    n: usize,
}

impl<K: Ord + Clone + Display> OptimalBST<K> {
    /// 创建最优BST求解器
    ///
    /// # 参数
    /// - `keys`: 有序关键字数组
    /// - `p`: 成功搜索概率（长度 = keys.len()）
    /// - `q`: 失败搜索概率（长度 = keys.len() + 1）
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::optimal_bst::OptimalBST;
    /// let keys = vec![10, 20, 30];
    /// let p = vec![0.3, 0.4, 0.1];    // 搜索各关键字的概率
    /// let q = vec![0.1, 0.05, 0.03, 0.02];  // 搜索失败的概率
    /// let mut opt_bst = OptimalBST::new(keys, p, q);
    /// ```
    pub fn new(keys: Vec<K>, p: Vec<f64>, q: Vec<f64>) -> Self {
        let n = keys.len();
        assert_eq!(p.len(), n);
        assert_eq!(q.len(), n + 1);
        
        // 验证概率和为1
        let sum: f64 = p.iter().sum::<f64>() + q.iter().sum::<f64>();
        assert!((sum - 1.0).abs() < 1e-6, "Probabilities must sum to 1");
        
        OptimalBST { keys, p, q, n }
    }

    /// 求解最优BST
    ///
    /// 使用动态规划算法计算最优BST结构
    pub fn solve(&self) -> OptimalBSTResult<K> {
        if self.n == 0 {
            return OptimalBSTResult {
                min_cost: self.q[0],
                root: None,
                root_table: vec![],
                cost_table: vec![vec![self.q[0]]],
            };
        }

        // 动态规划表
        // e[i][j] = 包含关键字i到j的最优BST的期望搜索代价
        let mut e = vec![vec![0.0; self.n + 2]; self.n + 2];
        // w[i][j] = 子树i..j的总概率
        let mut w = vec![vec![0.0; self.n + 2]; self.n + 2];
        // root[i][j] = 子树i..j的根
        let mut root = vec![vec![0; self.n + 2]; self.n + 2];

        // 初始化：单关键字的情况
        for i in 1..=self.n + 1 {
            e[i][i - 1] = self.q[i - 1];
            w[i][i - 1] = self.q[i - 1];
        }

        // 按子树长度递推
        for l in 1..=self.n {
            for i in 1..=self.n - l + 1 {
                let j = i + l - 1;
                e[i][j] = f64::INFINITY;
                w[i][j] = w[i][j - 1] + self.p[j - 1] + self.q[j];

                // 尝试每个可能的根
                for r in i..=j {
                    let t = e[i][r - 1] + e[r + 1][j] + w[i][j];
                    if t < e[i][j] {
                        e[i][j] = t;
                        root[i][j] = r;
                    }
                }
            }
        }

        // 构建BST
        let bst_root = self.build_tree(&root, 1, self.n);

        // 提取有用的代价表
        let mut cost_table = vec![vec![0.0; self.n]; self.n];
        for i in 1..=self.n {
            for j in i..=self.n {
                cost_table[i - 1][j - 1] = e[i][j];
            }
        }

        // 提取根表
        let mut root_table = vec![vec![0; self.n]; self.n];
        for i in 1..=self.n {
            for j in i..=self.n {
                root_table[i - 1][j - 1] = root[i][j] - 1; // 转换为0-based索引
            }
        }

        OptimalBSTResult {
            min_cost: e[1][self.n],
            root: bst_root,
            root_table,
            cost_table,
        }
    }

    /// 根据根表递归构建BST
    fn build_tree(&self, root: &[Vec<usize>], i: usize, j: usize) -> Option<Box<Node<K>>> {
        if i > j {
            return None;
        }

        let r = root[i][j];
        let mut node = Box::new(Node::new(self.keys[r - 1].clone()));
        node.left = self.build_tree(root, i, r - 1);
        node.right = self.build_tree(root, r + 1, j);
        Some(node)
    }

    /// 计算给定BST的搜索代价（用于验证）
    pub fn calculate_cost(&self, node: &Option<Box<Node<K>>>, depth: usize) -> f64 {
        match node {
            None => 0.0,
            Some(n) => {
                // 找到当前节点的概率
                let prob = self.keys.iter()
                    .position(|k| k == &n.key)
                    .map(|idx| self.p[idx])
                    .unwrap_or(0.0);
                
                let cost = prob * (depth + 1) as f64;
                cost + self.calculate_cost(&n.left, depth + 1)
                    + self.calculate_cost(&n.right, depth + 1)
            }
        }
    }
}

/// 简化版最优BST（只考虑成功搜索概率）
pub struct SimpleOptimalBST<K: Ord + Clone> {
    keys: Vec<K>,
    freq: Vec<usize>,
    n: usize,
}

impl<K: Ord + Clone + Display> SimpleOptimalBST<K> {
    pub fn new(keys: Vec<K>, freq: Vec<usize>) -> Self {
        assert_eq!(keys.len(), freq.len());
        SimpleOptimalBST {
            n: keys.len(),
            keys,
            freq,
        }
    }

    pub fn solve(&self) -> (usize, Option<Box<Node<K>>>) {
        if self.n == 0 {
            return (0, None);
        }

        // dp[i][j] = 关键字i到j的最优BST的最小搜索代价
        let mut dp = vec![vec![0; self.n]; self.n];
        let mut root = vec![vec![0; self.n]; self.n];

        // 初始化：单关键字
        for i in 0..self.n {
            dp[i][i] = self.freq[i];
            root[i][i] = i;
        }

        // 按区间长度递推
        for l in 2..=self.n {
            for i in 0..=self.n - l {
                let j = i + l - 1;
                dp[i][j] = usize::MAX;

                // 计算区间内的频率和
                let freq_sum: usize = self.freq[i..=j].iter().sum();

                // 尝试每个根
                for r in i..=j {
                    let left_cost = if r > i { dp[i][r - 1] } else { 0 };
                    let right_cost = if r < j { dp[r + 1][j] } else { 0 };
                    let cost = left_cost + right_cost + freq_sum;

                    if cost < dp[i][j] {
                        dp[i][j] = cost;
                        root[i][j] = r;
                    }
                }
            }
        }

        let tree_root = self.build_tree(&root, 0, self.n - 1);
        (dp[0][self.n - 1], tree_root)
    }

    fn build_tree(&self, root: &[Vec<usize>], i: usize, j: usize) -> Option<Box<Node<K>>> {
        if i > j {
            return None;
        }

        let r = root[i][j];
        let mut node = Box::new(Node::new(self.keys[r].clone()));
        node.left = if r > i { self.build_tree(root, i, r - 1) } else { None };
        node.right = if r < j { self.build_tree(root, r + 1, j) } else { None };
        Some(node)
    }
}

/// BST的可视化
pub fn format_tree<K: Ord + Clone + Display>(root: &Option<Box<Node<K>>>) -> String {
    fn helper<K: Ord + Clone + Display>(
        node: &Option<Box<Node<K>>>,
        prefix: &str,
        is_last: bool,
    ) -> String {
        match node {
            None => String::new(),
            Some(n) => {
                let mut result = String::new();
                result.push_str(prefix);
                if is_last {
                    result.push_str("└── ");
                } else {
                    result.push_str("├── ");
                }
                result.push_str(&n.key.to_string());
                result.push('\n');

                let new_prefix = if is_last {
                    format!("{}", prefix)
                } else {
                    format!("{}│   ", prefix)
                };

                let has_right = n.right.is_some();
                if n.left.is_some() {
                    result.push_str(&helper(&n.left, &new_prefix, !has_right));
                }
                if has_right {
                    result.push_str(&helper(&n.right, &new_prefix, true));
                }

                result
            }
        }
    }

    helper(root, "", true)
}

/// 中序遍历
pub fn inorder_traversal<K: Ord + Clone>(root: &Option<Box<Node<K>>>) -> Vec<K> {
    let mut result = Vec::new();
    fn helper<K: Ord + Clone>(node: &Option<Box<Node<K>>>, result: &mut Vec<K>) {
        if let Some(n) = node {
            helper(&n.left, result);
            result.push(n.key.clone());
            helper(&n.right, result);
        }
    }
    helper(root, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_bst() {
        // 简单例子：keys = [10, 12, 20], freq = [34, 8, 50]
        let keys = vec![10, 12, 20];
        let freq = vec![34, 8, 50];
        
        let opt = SimpleOptimalBST::new(keys.clone(), freq.clone());
        let (_cost, root) = opt.solve();
        
        // 最优结构应该是：12为根，10为左子，20为右子
        // 或者：10为根，右子树是12和20
        assert!(root.is_some());
        
        // 验证中序遍历结果正确
        let inorder = inorder_traversal(&root);
        assert_eq!(inorder, keys);
    }

    #[test]
    fn test_full_bst() {
        // 完整版本：包含失败概率
        let keys = vec![10, 20, 30];
        let p = vec![0.3, 0.4, 0.1];  // 成功概率
        let q = vec![0.1, 0.05, 0.03, 0.02];  // 失败概率
        
        let opt_bst = OptimalBST::new(keys, p, q);
        let result = opt_bst.solve();
        
        assert!(result.min_cost > 0.0);
        assert!(result.root.is_some());
    }

    #[test]
    fn test_single_key() {
        let keys = vec![42];
        let freq = vec![100];
        
        let opt = SimpleOptimalBST::new(keys.clone(), freq);
        let (cost, root) = opt.solve();
        
        assert_eq!(cost, 100);
        assert_eq!(inorder_traversal(&root), keys);
    }

    #[test]
    fn test_two_keys() {
        let keys = vec![10, 20];
        let freq = vec![90, 10];
        
        let opt = SimpleOptimalBST::new(keys.clone(), freq);
        let (_cost, root) = opt.solve();
        
        // 高频键应该在根
        assert!(root.is_some());
        let inorder = inorder_traversal(&root);
        assert_eq!(inorder, keys);
    }

    #[test]
    fn test_empty() {
        let keys: Vec<i32> = vec![];
        let freq: Vec<usize> = vec![];
        
        let opt = SimpleOptimalBST::new(keys, freq);
        let (cost, root) = opt.solve();
        
        assert_eq!(cost, 0);
        assert!(root.is_none());
    }

    #[test]
    fn test_format_tree() {
        let keys = vec![20, 10, 30];
        let freq = vec![1, 1, 1];
        
        let opt = SimpleOptimalBST::new(keys, freq);
        let (_, root) = opt.solve();
        
        let formatted = format_tree(&root);
        assert!(!formatted.is_empty());
        println!("{}", formatted);
    }

    #[test]
    fn test_probability_sum() {
        let keys = vec![1, 2, 3];
        let p = vec![0.5, 0.3, 0.2];
        let q = vec![0.0, 0.0, 0.0, 0.0];
        
        // 概率和应该为1
        let opt_bst = OptimalBST::new(keys, p, q);
        let result = opt_bst.solve();
        assert!(result.min_cost >= 1.0);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn dictionary_example() {
        println!("\n=== Dictionary Optimization Example ===");
        
        // 模拟词典中单词的搜索频率
        let words = vec!["apple", "banana", "cherry", "date", "elderberry"];
        let frequencies = vec![300, 150, 400, 100, 50];  // 搜索频率
        
        println!("Word frequencies:");
        for (word, freq) in words.iter().zip(frequencies.iter()) {
            println!("  {}: {}", word, freq);
        }
        
        let opt = SimpleOptimalBST::new(words.iter().map(|&s| s.to_string()).collect(), frequencies);
        let (min_cost, root) = opt.solve();
        
        println!("\nOptimal BST structure:");
        println!("{}", format_tree(&root));
        println!("Minimum search cost: {}", min_cost);
    }

    #[test]
    fn compiler_symbol_table() {
        println!("\n=== Compiler Symbol Table Example ===");
        
        // 编译器符号表优化
        // 变量名及其使用频率
        let identifiers = vec!["i", "j", "count", "sum", "result", "temp", "ptr"];
        let probs_success = vec![0.24, 0.19, 0.14, 0.12, 0.10, 0.10, 0.06];
        let probs_fail = vec![0.01, 0.005, 0.005, 0.005, 0.005, 0.005, 0.005, 0.01];
        
        println!("Identifier probabilities:");
        for (id, prob) in identifiers.iter().zip(probs_success.iter()) {
            println!("  {}: {:.2}%", id, prob * 100.0);
        }
        
        let opt_bst = OptimalBST::new(
            identifiers.iter().map(|&s| s.to_string()).collect(),
            probs_success,
            probs_fail,
        );
        
        let result = opt_bst.solve();
        
        println!("\nOptimal BST structure:");
        println!("{}", format_tree(&result.root));
        println!("\nMinimum expected search cost: {:.4}", result.min_cost);
        
        println!("\nRoot selection table:");
        for row in &result.root_table {
            println!("{:?}", row.iter().map(|&x| identifiers[x]).collect::<Vec<_>>());
        }
    }

    #[test]
    fn comparison_example() {
        println!("\n=== BST Structure Comparison ===");
        
        let keys = vec!["A", "B", "C", "D", "E"];
        let freq = vec![10, 50, 5, 30, 5];
        
        println!("Keys and frequencies:");
        for (k, f) in keys.iter().zip(freq.iter()) {
            println!("  {}: {}", k, f);
        }
        
        // 平衡BST（按中序构建）
        println!("\nBalanced BST (naive):");
        // 简单构建一个平衡树
        let balanced_root = build_balanced(&keys);
        println!("{}", format_tree(&balanced_root));
        
        // 最优BST
        let opt = SimpleOptimalBST::new(keys.iter().map(|&s| s.to_string()).collect(), freq);
        let (cost, optimal_root) = opt.solve();
        
        println!("\nOptimal BST:");
        println!("{}", format_tree(&optimal_root));
        println!("Minimum search cost: {}", cost);
    }

    fn build_balanced<K: Ord + Clone + Display>(keys: &[K]) -> Option<Box<Node<K>>> {
        if keys.is_empty() {
            return None;
        }
        let mid = keys.len() / 2;
        let mut node = Box::new(Node::new(keys[mid].clone()));
        node.left = build_balanced(&keys[..mid]);
        node.right = build_balanced(&keys[mid + 1..]);
        Some(node)
    }
}
