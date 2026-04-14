//! B树实现（适合磁盘存储）
//!
//! B树是一种自平衡的多路搜索树，专门为磁盘存储和外部存储器设计。
//! 通过减少磁盘I/O次数来提高性能，广泛应用于数据库和文件系统中。
//!
//! # 算法特性
//! - 多路分支：每个节点可以有多个子节点，减少树的高度
//! - 所有叶子节点在同一层：保证查找的稳定性
//! - 节点填充率：每个节点至少半满，保证空间利用率
//!
//! # B树性质（阶数为m）
//! - 每个节点最多有 m 个子节点
//! - 每个非根节点至少有 ⌈m/2⌉ 个子节点
//! - 根节点至少有2个子节点（除非它是叶子）
//! - 有 k 个子节点的非叶子节点有 k-1 个键
//! - 所有叶子节点在同一层
//!
//! # 时间复杂度
//! - 查找: O(log_m n)
//! - 插入: O(log_m n)
//! - 删除: O(log_m n)
//! - 空间: O(n)

use std::fmt::Debug;

/// B树的阶数（最大子节点数）
const DEFAULT_ORDER: usize = 4;

/// B树节点
#[derive(Debug, Clone)]
pub struct BTreeNode<T: Ord + Clone> {
    /// 节点中的键（已排序）
    keys: Vec<T>,
    /// 子节点
    children: Vec<Box<BTreeNode<T>>>,
    /// 是否为叶子节点
    is_leaf: bool,
}

impl<T: Ord + Clone> BTreeNode<T> {
    fn new(is_leaf: bool) -> Self {
        BTreeNode {
            keys: Vec::new(),
            children: Vec::new(),
            is_leaf,
        }
    }

    /// 节点是否已满
    fn is_full(&self, order: usize) -> bool {
        self.keys.len() == order - 1
    }

    /// 查找键的位置
    fn find_key(&self, key: &T) -> Result<usize, usize> {
        self.keys.binary_search(key)
    }
}

/// B树结构
#[derive(Debug)]
pub struct BTree<T: Ord + Clone> {
    root: Option<Box<BTreeNode<T>>>,
    order: usize,
    size: usize,
}

impl<T: Ord + Clone + Debug> BTree<T> {
    /// 创建指定阶数的B树
    ///
    /// # 参数
    /// - `order`: 阶数，每个节点最多有 order 个子节点
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::b_tree::BTree;
    /// let tree: BTree<i32> = BTree::new(4);
    /// ```
    pub fn new(order: usize) -> Self {
        assert!(order >= 3, "B-tree order must be at least 3");
        BTree {
            root: None,
            order,
            size: 0,
        }
    }

    /// 创建默认阶数的B树
    pub fn new_default() -> Self {
        Self::new(DEFAULT_ORDER)
    }

    /// 获取元素数量
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 查找元素
    pub fn contains(&self, key: &T) -> bool {
        Self::search_recursive(self.root.as_ref(), key)
    }

    fn search_recursive(node: Option<&Box<BTreeNode<T>>>, key: &T) -> bool {
        match node {
            None => false,
            Some(n) => {
                match n.find_key(key) {
                    Ok(_) => true,
                    Err(idx) => {
                        if n.is_leaf {
                            false
                        } else {
                            Self::search_recursive(Some(&n.children[idx]), key)
                        }
                    }
                }
            }
        }
    }

    /// 插入元素
    pub fn insert(&mut self, key: T) {
        if self.root.is_none() {
            let mut root = Box::new(BTreeNode::new(true));
            root.keys.push(key);
            self.root = Some(root);
            self.size = 1;
            return;
        }

        // 如果根节点已满，需要分裂
        if self.root.as_ref().unwrap().is_full(self.order) {
            let mut new_root = Box::new(BTreeNode::new(false));
            new_root.children.push(self.root.take().unwrap());
            Self::split_child(self.order, &mut new_root, 0);
            self.root = Some(new_root);
        }

        let order = self.order;
        let size = &mut self.size;
        let root = self.root.as_mut().unwrap();
        Self::insert_non_full(root, key, order, size);
    }

    /// 分裂子节点
    fn split_child(order: usize, parent: &mut BTreeNode<T>, idx: usize) {
        let mut new_node = Box::new(BTreeNode::new(parent.children[idx].is_leaf));
        let mid = (order - 1) / 2;

        // 移动后半部分的键到新节点
        let child = &mut parent.children[idx];
        new_node.keys = child.keys.split_off(mid + 1);

        // 如果不是叶子，移动子节点
        if !child.is_leaf {
            new_node.children = child.children.split_off(mid + 1);
        }

        // 提取中间键到父节点
        let middle_key = child.keys.pop().unwrap();
        parent.keys.insert(idx, middle_key);
        parent.children.insert(idx + 1, new_node);
    }

    /// 在非满节点中插入
    fn insert_non_full(node: &mut BTreeNode<T>, key: T, order: usize, size: &mut usize) {
        match node.find_key(&key) {
            Ok(_) => return, // 键已存在
            Err(mut idx) => {
                if node.is_leaf {
                    node.keys.insert(idx, key);
                    *size += 1;
                } else {
                    // 确保子节点不会满
                    if node.children[idx].is_full(order) {
                        Self::split_child(order, node, idx);
                        // 分裂后重新确定插入位置
                        if key > node.keys[idx] {
                            idx += 1;
                        }
                    }
                    Self::insert_non_full(&mut node.children[idx], key, order, size);
                }
            }
        }
    }

    /// 中序遍历获取所有键
    pub fn inorder_traversal(&self) -> Vec<&T> {
        let mut result = Vec::new();
        Self::inorder_recursive(self.root.as_ref(), &mut result);
        result
    }

    fn inorder_recursive<'a>(node: Option<&'a Box<BTreeNode<T>>>, result: &mut Vec<&'a T>) {
        if let Some(n) = node {
            for i in 0..n.keys.len() {
                if !n.is_leaf {
                    Self::inorder_recursive(Some(&n.children[i]), result);
                }
                result.push(&n.keys[i]);
            }
            if !n.is_leaf {
                Self::inorder_recursive(Some(&n.children[n.keys.len()]), result);
            }
        }
    }

    /// 范围查询 [start, end]
    pub fn range_query(&self, start: &T, end: &T) -> Vec<&T> {
        let mut result = Vec::new();
        Self::range_recursive(self.root.as_ref(), start, end, &mut result);
        result
    }

    fn range_recursive<'a>(
        node: Option<&'a Box<BTreeNode<T>>>,
        start: &T,
        end: &T,
        result: &mut Vec<&'a T>,
    ) {
        if let Some(n) = node {
            for i in 0..n.keys.len() {
                if !n.is_leaf {
                    Self::range_recursive(Some(&n.children[i]), start, end, result);
                }
                if n.keys[i] >= *start && n.keys[i] <= *end {
                    result.push(&n.keys[i]);
                }
            }
            if !n.is_leaf {
                Self::range_recursive(Some(&n.children[n.keys.len()]), start, end, result);
            }
        }
    }

    /// 获取树的高度
    pub fn height(&self) -> usize {
        Self::height_recursive(self.root.as_ref())
    }

    fn height_recursive(node: Option<&Box<BTreeNode<T>>>) -> usize {
        match node {
            None => 0,
            Some(n) => {
                if n.is_leaf {
                    1
                } else {
                    1 + Self::height_recursive(Some(&n.children[0]))
                }
            }
        }
    }
}

impl<T: Ord + Clone + Debug> Default for BTree<T> {
    fn default() -> Self {
        Self::new_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree: BTree<i32> = BTree::new_default();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.height(), 0);
    }

    #[test]
    fn test_insert_and_contains() {
        let mut tree = BTree::new(3); // 2-3树
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        
        assert!(tree.contains(&5));
        assert!(tree.contains(&3));
        assert!(tree.contains(&7));
        assert!(!tree.contains(&10));
        assert_eq!(tree.len(), 3);
    }

    #[test]
    fn test_insert_with_split() {
        let mut tree = BTree::new(4); // 阶数为4，最多3个键
        
        // 插入足够多的元素触发分裂
        for i in 0..20 {
            tree.insert(i);
        }
        
        assert_eq!(tree.len(), 20);
        
        // 验证所有元素都存在
        for i in 0..20 {
            assert!(tree.contains(&i), "Element {} not found", i);
        }
        
        // 树应该保持较低的高度
        assert!(tree.height() <= 4);
    }

    #[test]
    fn test_inorder_traversal() {
        let mut tree = BTree::new_default();
        let values = vec![5, 3, 7, 2, 4, 6, 8];
        for v in &values {
            tree.insert(*v);
        }
        
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec![&2, &3, &4, &5, &6, &7, &8]);
    }

    #[test]
    fn test_range_query() {
        let mut tree = BTree::new_default();
        for i in 0..100 {
            tree.insert(i);
        }
        
        let range_result = tree.range_query(&20, &30);
        assert_eq!(range_result.len(), 11);
        assert_eq!(range_result[0], &20);
        assert_eq!(range_result[10], &30);
    }

    #[test]
    fn test_large_tree() {
        let mut tree = BTree::new(100); // 大阶数
        let n = 10000;
        
        for i in 0..n {
            tree.insert(i);
        }
        
        // 大阶数B树应该有更小的树高
        let height = tree.height();
        assert!(height < 10, "Height {} too large for order 100 B-tree", height);
        
        // 验证所有元素
        for i in (0..n).step_by(100) {
            assert!(tree.contains(&i));
        }
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = BTree::new_default();
        tree.insert(5);
        tree.insert(5);
        tree.insert(5);
        
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_height_increase() {
        let mut tree = BTree::new(3); // 2-3树，更容易观察高度变化
        
        assert_eq!(tree.height(), 0);
        
        tree.insert(10);
        assert_eq!(tree.height(), 1);
        
        // 插入更多元素，观察高度增长
        for i in 0..100 {
            tree.insert(i);
        }
        
        // 高度应该保持对数增长
        let height = tree.height();
        let expected_max = ((100 as f64).ln() / (2.0f64.ln())).ceil() as usize + 1;
        assert!(height <= expected_max, "Height {} exceeds expected {}", height, expected_max);
    }

    #[test]
    fn test_generic_types() {
        let mut tree: BTree<String> = BTree::new(4);
        tree.insert("apple".to_string());
        tree.insert("banana".to_string());
        tree.insert("cherry".to_string());
        
        assert!(tree.contains(&"banana".to_string()));
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec!["apple", "banana", "cherry"]);
    }

    #[test]
    #[should_panic(expected = "B-tree order must be at least 3")]
    fn test_invalid_order() {
        let _: BTree<i32> = BTree::new(2);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn basic_usage() {
        println!("\n=== B-Tree Basic Usage ===");
        
        let mut tree = BTree::new(4);
        
        // 插入元素
        println!("Inserting: 30, 20, 40, 10, 25, 35, 50, 5, 15, 45");
        for &val in &[30, 20, 40, 10, 25, 35, 50, 5, 15, 45] {
            tree.insert(val);
        }
        
        println!("Tree height: {}", tree.height());
        println!("Elements in order: {:?}", tree.inorder_traversal());
        
        // 查找
        println!("Contains 25: {}", tree.contains(&25));
        println!("Contains 100: {}", tree.contains(&100));
        
        // 范围查询
        let range = tree.range_query(&15, &35);
        println!("Elements in range [15, 35]: {:?}", range);
    }

    #[test]
    fn database_index_simulation() {
        println!("\n=== Database Index Simulation ===");
        
        // 模拟数据库索引，使用较大的阶数
        let mut index = BTree::new(100);
        
        // 插入大量记录ID
        println!("Building index with 10000 records...");
        for id in 0..10000 {
            index.insert(id);
        }
        
        println!("Index height: {}", index.height());
        println!("Total records: {}", index.len());
        
        // 范围查询（分页）
        let page_size = 10;
        let page_num = 5;
        let start = page_num * page_size;
        let end = start + page_size - 1;
        
        let page = index.range_query(&start, &end);
        println!("Page {} (records {}-{}): {:?}", page_num, start, end, page);
    }

    #[test]
    fn compare_orders() {
        println!("\n=== Comparing Different Orders ===");
        
        let n = 1000;
        
        for &order in &[3, 10, 50, 100] {
            let mut tree = BTree::new(order);
            for i in 0..n {
                tree.insert(i);
            }
            println!("Order: {}, Height: {}", order, tree.height());
        }
    }
}
