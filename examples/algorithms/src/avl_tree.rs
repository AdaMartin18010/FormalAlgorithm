//! AVL树实现（自平衡二叉搜索树）
//!
//! AVL树是最早发明的自平衡二叉搜索树，通过在每个节点维护平衡因子（左右子树高度差），
//! 确保树的高度始终保持在 O(log n)，从而保证所有操作的时间复杂度为 O(log n)。
//!
//! # 算法特性
//! - 平衡因子：每个节点的左右子树高度差不超过1
//! - 旋转操作：单旋转和双旋转用于恢复平衡
//! - 严格平衡：比红黑树更严格的平衡条件
//!
//! # 时间复杂度
//! - 插入: O(log n)
//! - 删除: O(log n)
//! - 查找: O(log n)
//! - 空间: O(n)

use std::cmp::Ordering;
use std::fmt::Debug;

/// AVL树节点
#[derive(Debug)]
pub struct Node<T: Ord> {
    /// 节点值
    value: T,
    /// 左子树
    left: Option<Box<Node<T>>>,
    /// 右子树
    right: Option<Box<Node<T>>>,
    /// 节点高度（用于平衡计算）
    height: i32,
}

impl<T: Ord> Node<T> {
    /// 创建新节点
    fn new(value: T) -> Self {
        Node {
            value,
            left: None,
            right: None,
            height: 1,
        }
    }

    /// 获取节点高度
    fn height(node: &Option<Box<Node<T>>>) -> i32 {
        node.as_ref().map_or(0, |n| n.height)
    }

    /// 计算平衡因子
    fn balance_factor(&self) -> i32 {
        Self::height(&self.left) - Self::height(&self.right)
    }

    /// 更新节点高度
    fn update_height(&mut self) {
        self.height = 1 + std::cmp::max(Self::height(&self.left), Self::height(&self.right));
    }
}

/// AVL树结构
#[derive(Debug)]
pub struct AVLTree<T: Ord> {
    root: Option<Box<Node<T>>>,
    size: usize,
}

impl<T: Ord + Debug> AVLTree<T> {
    /// 创建空AVL树
    pub fn new() -> Self {
        AVLTree { root: None, size: 0 }
    }

    /// 获取树中元素数量
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查树是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 插入元素
    ///
    /// # 示例
    /// ```
    /// let mut tree = AVLTree::new();
    /// tree.insert(5);
    /// tree.insert(3);
    /// tree.insert(7);
    /// ```
    pub fn insert(&mut self, value: T) {
        self.root = Self::insert_recursive(self.root.take(), value);
        self.size += 1;
    }

    /// 递归插入并平衡
    fn insert_recursive(node: Option<Box<Node<T>>>, value: T) -> Option<Box<Node<T>>> {
        let mut node = match node {
            None => return Some(Box::new(Node::new(value))),
            Some(n) => n,
        };

        // 标准BST插入
        match value.cmp(&node.value) {
            Ordering::Less => {
                node.left = Self::insert_recursive(node.left.take(), value);
            }
            Ordering::Greater => {
                node.right = Self::insert_recursive(node.right.take(), value);
            }
            Ordering::Equal => {
                // 重复值，不插入
                return Some(node);
            }
        }

        // 更新高度
        node.update_height();

        // 获取平衡因子并重新平衡
        let balance = node.balance_factor();

        // 左左情况
        if balance > 1 && value < node.left.as_ref().unwrap().value {
            return Some(Self::rotate_right(node));
        }

        // 右右情况
        if balance < -1 && value > node.right.as_ref().unwrap().value {
            return Some(Self::rotate_left(node));
        }

        // 左右情况
        if balance > 1 && value > node.left.as_ref().unwrap().value {
            node.left = Some(Self::rotate_left(node.left.take().unwrap()));
            return Some(Self::rotate_right(node));
        }

        // 右左情况
        if balance < -1 && value < node.right.as_ref().unwrap().value {
            node.right = Some(Self::rotate_right(node.right.take().unwrap()));
            return Some(Self::rotate_left(node));
        }

        Some(node)
    }

    /// 右旋操作
    fn rotate_right(mut y: Box<Node<T>>) -> Box<Node<T>> {
        let mut x = y.left.take().unwrap();
        let t2 = x.right.take();

        x.right = Some(y);
        x.right.as_mut().unwrap().left = t2;

        x.right.as_mut().unwrap().update_height();
        x.update_height();

        x
    }

    /// 左旋操作
    fn rotate_left(mut x: Box<Node<T>>) -> Box<Node<T>> {
        let mut y = x.right.take().unwrap();
        let t2 = y.left.take();

        y.left = Some(x);
        y.left.as_mut().unwrap().right = t2;

        y.left.as_mut().unwrap().update_height();
        y.update_height();

        y
    }

    /// 查找元素
    ///
    /// # 返回值
    /// - `true`: 元素存在
    /// - `false`: 元素不存在
    pub fn contains(&self, value: &T) -> bool {
        Self::contains_recursive(&self.root, value)
    }

    fn contains_recursive(node: &Option<Box<Node<T>>>, value: &T) -> bool {
        match node {
            None => false,
            Some(n) => match value.cmp(&n.value) {
                Ordering::Equal => true,
                Ordering::Less => Self::contains_recursive(&n.left, value),
                Ordering::Greater => Self::contains_recursive(&n.right, value),
            },
        }
    }

    /// 删除元素
    pub fn remove(&mut self, value: &T) -> bool {
        if self.contains(value) {
            self.root = Self::remove_recursive(self.root.take(), value);
            self.size -= 1;
            true
        } else {
            false
        }
    }

    fn remove_recursive(node: Option<Box<Node<T>>>, value: &T) -> Option<Box<Node<T>>> {
        let mut node = match node {
            None => return None,
            Some(n) => n,
        };

        match value.cmp(&node.value) {
            Ordering::Less => {
                node.left = Self::remove_recursive(node.left.take(), value);
            }
            Ordering::Greater => {
                node.right = Self::remove_recursive(node.right.take(), value);
            }
            Ordering::Equal => {
                // 找到要删除的节点
                if node.left.is_none() {
                    return node.right;
                } else if node.right.is_none() {
                    return node.left;
                } else {
                    // 有两个子节点，找到右子树的最小值
                    let min_val = Self::find_min(&node.right);
                    if let Some(min) = min_val {
                        node.value = min;
                        node.right = Self::remove_recursive(node.right.take(), &node.value);
                    }
                }
            }
        }

        if node.left.is_none() && node.right.is_none() {
            node.height = 1;
            return Some(node);
        }

        node.update_height();

        let balance = node.balance_factor();

        // 左左情况
        if balance > 1 && Node::balance_factor(node.left.as_ref().unwrap()) >= 0 {
            return Some(Self::rotate_right(node));
        }

        // 左右情况
        if balance > 1 && Node::balance_factor(node.left.as_ref().unwrap()) < 0 {
            node.left = Some(Self::rotate_left(node.left.take().unwrap()));
            return Some(Self::rotate_right(node));
        }

        // 右右情况
        if balance < -1 && Node::balance_factor(node.right.as_ref().unwrap()) <= 0 {
            return Some(Self::rotate_left(node));
        }

        // 右左情况
        if balance < -1 && Node::balance_factor(node.right.as_ref().unwrap()) > 0 {
            node.right = Some(Self::rotate_right(node.right.take().unwrap()));
            return Some(Self::rotate_left(node));
        }

        Some(node)
    }

    fn find_min(node: &Option<Box<Node<T>>>) -> Option<T>
    where
        T: Clone,
    {
        match node {
            None => None,
            Some(n) => {
                if n.left.is_none() {
                    Some(n.value.clone())
                } else {
                    Self::find_min(&n.left)
                }
            }
        }
    }

    /// 中序遍历（按升序输出）
    pub fn inorder_traversal(&self) -> Vec<&T> {
        let mut result = Vec::new();
        Self::inorder_recursive(&self.root, &mut result);
        result
    }

    fn inorder_recursive<'a>(node: &'a Option<Box<Node<T>>>, result: &mut Vec<&'a T>) {
        if let Some(n) = node {
            Self::inorder_recursive(&n.left, result);
            result.push(&n.value);
            Self::inorder_recursive(&n.right, result);
        }
    }

    /// 获取树的高度
    pub fn height(&self) -> i32 {
        Node::height(&self.root)
    }
}

impl<T: Ord + Debug> Default for AVLTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree: AVLTree<i32> = AVLTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.height(), 0);
    }

    #[test]
    fn test_insert_and_contains() {
        let mut tree = AVLTree::new();
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
    fn test_balance_after_insertion() {
        let mut tree = AVLTree::new();
        // 插入会导致左旋的数据: 1, 2, 3
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        
        // 树应该被平衡
        assert!(tree.height() <= 2);
        assert!(tree.contains(&1));
        assert!(tree.contains(&2));
        assert!(tree.contains(&3));
    }

    #[test]
    fn test_remove() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.insert(2);
        tree.insert(4);
        
        assert!(tree.remove(&3));
        assert!(!tree.contains(&3));
        assert_eq!(tree.len(), 4);
        
        // 删除不存在的元素
        assert!(!tree.remove(&100));
    }

    #[test]
    fn test_remove_leaf() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        
        assert!(tree.remove(&3));
        assert!(!tree.contains(&3));
        assert!(tree.contains(&5));
        assert!(tree.contains(&7));
    }

    #[test]
    fn test_inorder_traversal() {
        let mut tree = AVLTree::new();
        let values = vec![5, 3, 7, 2, 4, 6, 8];
        for v in &values {
            tree.insert(*v);
        }
        
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec![&2, &3, &4, &5, &6, &7, &8]);
    }

    #[test]
    fn test_large_tree() {
        let mut tree = AVLTree::new();
        let n = 1000;
        
        // 插入大量数据
        for i in 0..n {
            tree.insert(i);
        }
        
        // 验证高度保持对数级
        let height = tree.height();
        let max_height = (n as f64).log2() as i32 + 2;
        assert!(height <= max_height, "Tree height {} exceeds expected max {}", height, max_height);
        
        // 验证所有元素都存在
        for i in 0..n {
            assert!(tree.contains(&i), "Element {} not found", i);
        }
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = AVLTree::new();
        tree.insert(5);
        tree.insert(5);
        tree.insert(5);
        
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_generic_types() {
        let mut tree: AVLTree<String> = AVLTree::new();
        tree.insert("apple".to_string());
        tree.insert("banana".to_string());
        tree.insert("cherry".to_string());
        
        assert!(tree.contains(&"banana".to_string()));
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec!["apple", "banana", "cherry"]);
    }
}

/// 使用示例
///
/// 运行: cargo test --examples avl_tree::example
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn basic_usage() {
        println!("\n=== AVL Tree Basic Usage ===");
        
        let mut tree = AVLTree::new();
        
        // 插入元素
        println!("Inserting: 30, 20, 40, 10, 25, 35, 50");
        for &val in &[30, 20, 40, 10, 25, 35, 50] {
            tree.insert(val);
        }
        
        println!("Tree height: {}", tree.height());
        println!("Elements in order: {:?}", tree.inorder_traversal());
        
        // 查找
        println!("Contains 25: {}", tree.contains(&25));
        println!("Contains 100: {}", tree.contains(&100));
        
        // 删除
        println!("Removing 20...");
        tree.remove(&20);
        println!("Elements after removal: {:?}", tree.inorder_traversal());
        
        // 插入更多元素以触发旋转
        println!("\nInserting to trigger rotations: 5, 3, 1");
        tree.insert(5);
        tree.insert(3);
        tree.insert(1);
        println!("Tree height after insertions: {}", tree.height());
        println!("Final elements: {:?}", tree.inorder_traversal());
    }
}
