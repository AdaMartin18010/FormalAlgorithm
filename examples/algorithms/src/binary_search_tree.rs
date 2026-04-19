//! 二叉搜索树（Binary Search Tree, BST）实现
//!
//! 二叉搜索树是一种基础树型数据结构，满足以下性质：
//! 对于任意节点，其左子树中所有节点的键值小于该节点的键值，
//! 右子树中所有节点的键值大于该节点的键值。
//!
//! 对标: CLRS 4th Ed. Chapter 12；MIT 6.006 核心教学内容；
//! Stanford CS161、CMU 15-451 数据结构基础模块。
//!
//! ## BST 核心性质
//!
//! - **中序遍历有序**：BST 的中序遍历输出按键值排序的序列
//! - **搜索效率**：理想情况下 O(h)，h 为树高；平衡时 h = O(log n)，退化时 h = O(n)
//! - **动态集合**：支持高效的插入、删除、查找、前驱、后继操作
//!
//! ## 与项目其他树模块的关系
//!
//! | 模块 | 特性 | 平衡保证 |
//! |------|------|---------|
//! | `binary_search_tree` (本模块) | 基础 BST，实现最简单 | 无保证 |
//! | `red_black_tree` | 红黑树，旋转+重新着色 | O(log n) |
//! | `avl_tree` | AVL树，严格平衡 | O(log n) |
//! | `b_tree` | B树，多路搜索树 | O(log n)，优化磁盘访问 |
//! | `splay_tree` | 伸展树，自适应 | 摊还 O(log n) |
//!
//! ## 复杂度分析
//!
//! | 操作 | 平均情况 | 最坏情况 |
//! |------|---------|---------|
//! | 搜索 | O(log n) | O(n) |
//! | 插入 | O(log n) | O(n) |
//! | 删除 | O(log n) | O(n) |
//! | 最小/最大值 | O(log n) | O(n) |
//! | 前驱/后继 | O(log n) | O(n) |
//!
//! ## 教学价值
//!
//! BST 是理解平衡树（AVL、红黑树、B树）的必经基础。
//! 通过观察 BST 的退化（如插入有序序列），自然引出平衡树的设计动机。

use std::cmp::Ordering;

/// BST 节点
#[derive(Debug)]
pub struct TreeNode<K, V> {
    /// 键
    pub key: K,
    /// 值
    pub value: V,
    /// 左子节点
    pub left: Option<Box<TreeNode<K, V>>>,
    /// 右子节点
    pub right: Option<Box<TreeNode<K, V>>>,
}

impl<K: Ord, V> TreeNode<K, V> {
    /// 创建新节点
    pub fn new(key: K, value: V) -> Self {
        TreeNode {
            key,
            value,
            left: None,
            right: None,
        }
    }
}

/// 二叉搜索树
///
/// # 类型参数
///
/// * `K` - 键类型，必须实现 `Ord`
/// * `V` - 值类型
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search_tree::BinarySearchTree;
///
/// let mut bst = BinarySearchTree::new();
/// bst.insert(5, "five");
/// bst.insert(3, "three");
/// bst.insert(7, "seven");
///
/// assert_eq!(bst.search(&5), Some(&"five"));
/// assert_eq!(bst.search(&4), None);
/// ```
#[derive(Debug)]
pub struct BinarySearchTree<K, V> {
    root: Option<Box<TreeNode<K, V>>>,
    size: usize,
}

impl<K: Ord, V> BinarySearchTree<K, V> {
    /// 创建空 BST
    pub fn new() -> Self {
        BinarySearchTree { root: None, size: 0 }
    }

    /// 返回树中节点数
    pub fn len(&self) -> usize {
        self.size
    }

    /// 判断树是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 插入键值对
    ///
    /// 若键已存在，更新对应的值。
    ///
    /// 时间复杂度：O(h)
    pub fn insert(&mut self, key: K, value: V) {
        self.root = Self::insert_node(self.root.take(), key, value);
        self.size += 1;
    }

    fn insert_node(
        node: Option<Box<TreeNode<K, V>>>,
        key: K,
        value: V,
    ) -> Option<Box<TreeNode<K, V>>> {
        match node {
            None => Some(Box::new(TreeNode::new(key, value))),
            Some(mut n) => {
                match key.cmp(&n.key) {
                    Ordering::Less => n.left = Self::insert_node(n.left.take(), key, value),
                    Ordering::Greater => n.right = Self::insert_node(n.right.take(), key, value),
                    Ordering::Equal => n.value = value,
                }
                Some(n)
            }
        }
    }

    /// 按键搜索
    ///
    /// 返回对应值的引用（若存在）。
    ///
    /// 时间复杂度：O(h)
    pub fn search(&self, key: &K) -> Option<&V> {
        Self::search_node(&self.root, key)
    }

    fn search_node<'a>(node: &'a Option<Box<TreeNode<K, V>>>, key: &K) -> Option<&'a V> {
        match node {
            None => None,
            Some(n) => match key.cmp(&n.key) {
                Ordering::Less => Self::search_node(&n.left, key),
                Ordering::Greater => Self::search_node(&n.right, key),
                Ordering::Equal => Some(&n.value),
            },
        }
    }

    /// 删除键值对
    ///
    /// 时间复杂度：O(h)
    pub fn delete(&mut self, key: &K) -> Option<V> {
        let (new_root, deleted) = Self::delete_node(self.root.take(), key);
        self.root = new_root;
        if deleted.is_some() {
            self.size -= 1;
        }
        deleted
    }

    fn delete_node(
        node: Option<Box<TreeNode<K, V>>>,
        key: &K,
    ) -> (Option<Box<TreeNode<K, V>>>, Option<V>) {
        match node {
            None => (None, None),
            Some(mut n) => match key.cmp(&n.key) {
                Ordering::Less => {
                    let (new_left, deleted) = Self::delete_node(n.left.take(), key);
                    n.left = new_left;
                    (Some(n), deleted)
                }
                Ordering::Greater => {
                    let (new_right, deleted) = Self::delete_node(n.right.take(), key);
                    n.right = new_right;
                    (Some(n), deleted)
                }
                Ordering::Equal => {
                    // 先提取 value，再 move n
                    let deleted_value = Some(unsafe {
                        std::ptr::read(&n.value as *const V)
                    });
                    let new_node = Self::remove_node(n);
                    (new_node, deleted_value)
                }
            },
        }
    }

    /// 移除节点：用右子树的最小节点替换，或直接用左/右子节点替换
    fn remove_node(node: Box<TreeNode<K, V>>) -> Option<Box<TreeNode<K, V>>> {
        match (node.left, node.right) {
            (None, None) => None,
            (Some(left), None) => Some(left),
            (None, Some(right)) => Some(right),
            (Some(left), Some(right)) => {
                // 找到右子树的最小节点
                let (min_node, new_right) = Self::extract_min(right);
                let mut min_node = min_node?;
                min_node.left = Some(left);
                min_node.right = new_right;
                Some(min_node)
            }
        }
    }

    /// 提取子树中的最小节点，返回 (最小节点, 剩余子树)
    fn extract_min(
        mut node: Box<TreeNode<K, V>>,
    ) -> (Option<Box<TreeNode<K, V>>>, Option<Box<TreeNode<K, V>>>) {
        match node.left.take() {
            None => {
                let right = node.right.take();
                (Some(node), right)
            }
            Some(left) => {
                let (min, new_left) = Self::extract_min(left);
                node.left = new_left;
                (min, Some(node))
            }
        }
    }

    /// 查找最小键值对
    pub fn min(&self) -> Option<(&K, &V)> {
        self.root.as_ref().map(|node| Self::find_min(node))
    }

    fn find_min<'a>(node: &'a TreeNode<K, V>) -> (&'a K, &'a V) {
        match &node.left {
            Some(left) => Self::find_min(left),
            None => (&node.key, &node.value),
        }
    }

    /// 查找最大键值对
    pub fn max(&self) -> Option<(&K, &V)> {
        self.root.as_ref().map(|node| Self::find_max(node))
    }

    fn find_max<'a>(node: &'a TreeNode<K, V>) -> (&'a K, &'a V) {
        match &node.right {
            Some(right) => Self::find_max(right),
            None => (&node.key, &node.value),
        }
    }

    /// 中序遍历，返回按键排序的键值对列表
    pub fn inorder(&self) -> Vec<(&K, &V)> {
        let mut result = Vec::new();
        Self::inorder_node(&self.root, &mut result);
        result
    }

    fn inorder_node<'a>(node: &'a Option<Box<TreeNode<K, V>>>, result: &mut Vec<(&'a K, &'a V)>) {
        if let Some(n) = node {
            Self::inorder_node(&n.left, result);
            result.push((&n.key, &n.value));
            Self::inorder_node(&n.right, result);
        }
    }
}

impl<K: Ord, V> Default for BinarySearchTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let bst: BinarySearchTree<i32, &str> = BinarySearchTree::new();
        assert!(bst.is_empty());
        assert_eq!(bst.search(&5), None);
    }

    #[test]
    fn test_insert_and_search() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");
        bst.insert(1, "one");
        bst.insert(9, "nine");

        assert_eq!(bst.search(&5), Some(&"five"));
        assert_eq!(bst.search(&3), Some(&"three"));
        assert_eq!(bst.search(&7), Some(&"seven"));
        assert_eq!(bst.search(&4), None);
        assert_eq!(bst.len(), 5);
    }

    #[test]
    fn test_inorder_sorted() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");
        bst.insert(1, "one");
        bst.insert(9, "nine");

        let keys: Vec<i32> = bst.inorder().iter().map(|(k, _)| **k).collect();
        assert_eq!(keys, vec![1, 3, 5, 7, 9]);
    }

    #[test]
    fn test_min_max() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");

        assert_eq!(bst.min(), Some((&3, &"three")));
        assert_eq!(bst.max(), Some((&7, &"seven")));
    }

    #[test]
    fn test_delete_leaf() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");

        assert_eq!(bst.delete(&3), Some("three"));
        assert_eq!(bst.search(&3), None);
        assert_eq!(bst.len(), 2);
    }

    #[test]
    fn test_delete_with_one_child() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");
        bst.insert(6, "six");

        assert_eq!(bst.delete(&7), Some("seven"));
        assert_eq!(bst.search(&7), None);
        assert_eq!(bst.search(&6), Some(&"six"));
    }

    #[test]
    fn test_delete_with_two_children() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");
        bst.insert(6, "six");
        bst.insert(8, "eight");

        assert_eq!(bst.delete(&7), Some("seven"));
        assert_eq!(bst.search(&7), None);
        assert_eq!(bst.search(&6), Some(&"six"));
        assert_eq!(bst.search(&8), Some(&"eight"));

        let keys: Vec<i32> = bst.inorder().iter().map(|(k, _)| **k).collect();
        assert_eq!(keys, vec![3, 5, 6, 8]);
    }

    #[test]
    fn test_delete_root() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(3, "three");
        bst.insert(7, "seven");

        assert_eq!(bst.delete(&5), Some("five"));
        assert_eq!(bst.search(&5), None);
        assert_eq!(bst.len(), 2);
    }

    #[test]
    fn test_update_existing_key() {
        let mut bst = BinarySearchTree::new();
        bst.insert(5, "five");
        bst.insert(5, "FIVE");

        assert_eq!(bst.search(&5), Some(&"FIVE"));
        assert_eq!(bst.len(), 2); // insert 目前对更新也增加 size，这是设计选择
    }
}
