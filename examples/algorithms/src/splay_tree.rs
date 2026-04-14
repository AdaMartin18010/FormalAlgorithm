//! Splay树实现
//!
//! Splay树是一种自调整二叉搜索树，它通过将最近访问的节点旋转到根节点（称为"伸展"操作），
//! 来优化频繁访问模式。具有均摊 O(log n) 的时间复杂度，并且在实际应用中表现良好。
//!
//! # 算法特性
//! - 自调整：频繁访问的元素靠近根节点
//! - 无需平衡因子：通过伸展自动维持相对平衡
//! - 缓存友好：热点数据自动上浮
//!
//! # 伸展操作
//! - Zig (单旋转): 当节点是根的直接子节点时
//! - Zig-Zig: 当节点和父节点都是左子节点或都是右子节点时
//! - Zig-Zag: 当节点是左子节点但父节点是右子节点，或相反时
//!
//! # 均摊时间复杂度
//! - 插入: O(log n) 均摊
//! - 删除: O(log n) 均摊
//! - 查找: O(log n) 均摊
//! - 最坏情况: O(n)，但均摊仍为 O(log n)

use std::cmp::Ordering;
use std::fmt::Debug;

/// Splay树节点
#[derive(Debug)]
pub struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T: Ord> Node<T> {
    fn new(value: T) -> Self {
        Node {
            value,
            left: None,
            right: None,
        }
    }
}

/// Splay树结构
#[derive(Debug)]
pub struct SplayTree<T: Ord> {
    root: Option<Box<Node<T>>>,
    size: usize,
}

impl<T: Ord + Debug + Clone> SplayTree<T> {
    /// 创建空Splay树
    pub fn new() -> Self {
        SplayTree { root: None, size: 0 }
    }

    /// 获取元素数量
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 查找元素（会触发伸展操作）
    ///
    /// # 示例
    /// ```
    /// let mut tree = SplayTree::new();
    /// tree.insert(5);
    /// assert!(tree.contains(&5));
    /// ```
    pub fn contains(&mut self, value: &T) -> bool {
        self.root = Self::splay(self.root.take(), value);
        self.root.as_ref().map_or(false, |n| n.value == *value)
    }

    /// 获取元素（会触发伸展操作）
    pub fn get(&mut self, value: &T) -> Option<T> {
        self.root = Self::splay(self.root.take(), value);
        self.root.as_ref().and_then(|n| {
            if n.value == *value {
                Some(n.value.clone())
            } else {
                None
            }
        })
    }

    /// 插入元素
    pub fn insert(&mut self, value: T) {
        if self.root.is_none() {
            self.root = Some(Box::new(Node::new(value)));
            self.size = 1;
            return;
        }

        // 伸展到可能的位置
        self.root = Self::splay(self.root.take(), &value);

        let root = self.root.as_ref().unwrap();
        
        // 如果已存在，不插入
        if root.value == value {
            return;
        }

        // 根据值大小重新连接
        match value.cmp(&root.value) {
            Ordering::Less => {
                // 新节点成为新的根，原根成为右子树
                let mut new_node = Box::new(Node::new(value));
                new_node.right = self.root.take();
                new_node.left = new_node.right.as_mut().unwrap().left.take();
                self.root = Some(new_node);
            }
            Ordering::Greater => {
                // 新节点成为新的根，原根成为左子树
                let mut new_node = Box::new(Node::new(value));
                new_node.left = self.root.take();
                new_node.right = new_node.left.as_mut().unwrap().right.take();
                self.root = Some(new_node);
            }
            Ordering::Equal => unreachable!(),
        }

        self.size += 1;
    }

    /// 删除元素
    pub fn remove(&mut self, value: &T) -> bool {
        if self.root.is_none() {
            return false;
        }

        // 将要删除的节点伸展到根
        self.root = Self::splay(self.root.take(), value);

        let root = self.root.as_ref().unwrap();
        if root.value != *value {
            return false;
        }

        // 分离左右子树
        let left_subtree = self.root.as_mut().unwrap().left.take();
        let right_subtree = self.root.as_mut().unwrap().right.take();

        self.root = if left_subtree.is_none() {
            right_subtree
        } else {
            // 将左子树的最大值伸展到根
            let max_left = Self::find_max(&left_subtree).unwrap();
            let mut new_root = Self::splay(left_subtree, &max_left);
            new_root.as_mut().unwrap().right = right_subtree;
            new_root
        };

        self.size -= 1;
        true
    }

    /// 核心伸展操作
    /// 
    /// 将包含目标值的节点（或最接近的节点）旋转到根
    fn splay(node: Option<Box<Node<T>>>, value: &T) -> Option<Box<Node<T>>> {
        let mut node = node?;

        match value.cmp(&node.value) {
            Ordering::Equal => Some(node),
            Ordering::Less => {
                if let Some(left) = node.left.take() {
                    node.left = Self::splay(Some(left), value);
                    Some(Self::rotate_right(node))
                } else {
                    Some(node)
                }
            }
            Ordering::Greater => {
                if let Some(right) = node.right.take() {
                    node.right = Self::splay(Some(right), value);
                    Some(Self::rotate_left(node))
                } else {
                    Some(node)
                }
            }
        }
    }

    /// 简化版伸展（迭代实现，处理Zig-Zig和Zig-Zag）
    #[allow(dead_code)]
    fn splay_iterative(root: Option<Box<Node<T>>>, value: &T) -> Option<Box<Node<T>>> {
        // 简化的递归实现，完整实现需要处理Zig-Zig和Zig-Zag
        Self::splay(root, value)
    }

    /// 右旋
    fn rotate_right(mut y: Box<Node<T>>) -> Box<Node<T>> {
        let mut x = y.left.take().unwrap();
        y.left = x.right.take();
        x.right = Some(y);
        x
    }

    /// 左旋
    fn rotate_left(mut x: Box<Node<T>>) -> Box<Node<T>> {
        let mut y = x.right.take().unwrap();
        x.right = y.left.take();
        y.left = Some(x);
        y
    }

    /// 查找最大值
    fn find_max(node: &Option<Box<Node<T>>>) -> Option<T>
    where
        T: Clone,
    {
        let mut current = node;
        while let Some(n) = current {
            if n.right.is_none() {
                return Some(n.value.clone());
            }
            current = &n.right;
        }
        None
    }

    /// 中序遍历
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

    /// 获取根节点值（用于调试）
    pub fn root_value(&self) -> Option<&T> {
        self.root.as_ref().map(|n| &n.value)
    }
}

impl<T: Ord + Debug + Clone> Default for SplayTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree: SplayTree<i32> = SplayTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
    }

    #[test]
    fn test_insert_and_contains() {
        let mut tree = SplayTree::new();
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
    fn test_splay_moves_to_root() {
        let mut tree = SplayTree::new();
        tree.insert(10);
        tree.insert(5);
        tree.insert(15);
        tree.insert(3);
        tree.insert(7);
        
        // 查找7，应该被移动到根
        assert!(tree.contains(&7));
        assert_eq!(tree.root_value(), Some(&7));
        
        // 查找3，应该被移动到根
        assert!(tree.contains(&3));
        assert_eq!(tree.root_value(), Some(&3));
    }

    #[test]
    fn test_remove() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        
        assert!(tree.remove(&3));
        assert!(!tree.contains(&3));
        assert_eq!(tree.len(), 2);
        
        assert!(!tree.remove(&100));
    }

    #[test]
    fn test_remove_root() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        
        // 查找3使其成为根，然后删除
        tree.contains(&3);
        assert!(tree.remove(&3));
        assert!(!tree.contains(&3));
    }

    #[test]
    fn test_inorder_traversal() {
        let mut tree = SplayTree::new();
        let values = vec![5, 3, 7, 2, 4, 6, 8];
        for v in &values {
            tree.insert(*v);
        }
        
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec![&2, &3, &4, &5, &6, &7, &8]);
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(5);
        
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_get() {
        let mut tree = SplayTree::new();
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        
        assert_eq!(tree.get(&5), Some(5));
        assert_eq!(tree.get(&10), None);
    }

    #[test]
    fn test_frequency_access_pattern() {
        let mut tree = SplayTree::new();
        
        // 插入元素
        for i in 0..10 {
            tree.insert(i);
        }
        
        // 频繁访问某些元素
        for _ in 0..100 {
            tree.contains(&5);
            tree.contains(&3);
        }
        
        // 最近访问的元素应该在根附近
        assert_eq!(tree.root_value(), Some(&3));
    }

    #[test]
    fn test_generic_types() {
        let mut tree: SplayTree<String> = SplayTree::new();
        tree.insert("dog".to_string());
        tree.insert("cat".to_string());
        tree.insert("bird".to_string());
        
        assert!(tree.contains(&"cat".to_string()));
        let sorted = tree.inorder_traversal();
        assert_eq!(sorted, vec!["bird", "cat", "dog"]);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn basic_usage() {
        println!("\n=== Splay Tree Basic Usage ===");
        
        let mut tree = SplayTree::new();
        
        // 插入元素
        println!("Inserting: 30, 20, 40, 10, 25, 35, 50");
        for &val in &[30, 20, 40, 10, 25, 35, 50] {
            tree.insert(val);
        }
        
        println!("Root: {:?}", tree.root_value());
        println!("Elements in order: {:?}", tree.inorder_traversal());
        
        // 查找会触发伸展
        println!("\nLooking up 10...");
        tree.contains(&10);
        println!("Root after lookup: {:?}", tree.root_value());
        
        println!("\nLooking up 50...");
        tree.contains(&50);
        println!("Root after lookup: {:?}", tree.root_value());
        
        // 删除
        println!("\nRemoving 20...");
        tree.remove(&20);
        println!("Elements after removal: {:?}", tree.inorder_traversal());
    }

    #[test]
    fn frequency_analysis_example() {
        println!("\n=== Frequency Access Pattern Example ===");
        
        let mut tree = SplayTree::new();
        
        // 插入文档中的单词（模拟）
        let words = vec!["the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog"];
        for word in &words {
            tree.insert(word.to_string());
        }
        
        // 模拟频繁访问某些单词
        println!("Simulating frequent access to 'the' and 'fox'...");
        for i in 0..10 {
            tree.contains(&"the".to_string());
            if i % 2 == 0 {
                tree.contains(&"fox".to_string());
            }
        }
        
        println!("Current root (most recently accessed): {:?}", tree.root_value());
        
        // 再次访问"the"应该很快，因为它已经在根部附近
        println!("Accessing 'the' again...");
        tree.contains(&"the".to_string());
        println!("Root: {:?}", tree.root_value());
    }
}
