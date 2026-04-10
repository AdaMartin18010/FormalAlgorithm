//! 红黑树 (Red-Black Tree)
//!
//! 红黑树是一种自平衡二叉搜索树，保证在最坏情况下基本操作
//! (插入、删除、查找)的时间复杂度为O(log n)。
//!
//! # 红黑树性质
//! 1. 每个节点是红色或黑色
//! 2. 根节点是黑色
//! 3. 每个叶子(NIL)是黑色
//! 4. 红色节点的子节点必须是黑色(不能有两个连续的红色节点)
//! 5. 从任一节点到其每个叶子的所有路径包含相同数目的黑色节点
//!
//! # 算法复杂度
//! - 查找: O(log n)
//! - 插入: O(log n)
//! - 删除: O(log n)
//! - 空间复杂度: O(n)

use std::cmp::Ordering;
use std::fmt::Debug;

/// 节点颜色
#[derive(Debug, Clone, Copy, PartialEq)]
enum Color {
    Red,
    Black,
}

/// 红黑树节点
#[derive(Debug)]
struct Node<K: Ord + Debug, V: Debug> {
    /// 键
    key: K,
    /// 值
    value: V,
    /// 节点颜色
    color: Color,
    /// 左子节点
    left: Option<Box<Node<K, V>>>,
    /// 右子节点
    right: Option<Box<Node<K, V>>>,
    /// 子树节点数(用于顺序统计)
    size: usize,
}

impl<K: Ord + Debug, V: Debug> Node<K, V> {
    /// 创建新节点(默认为红色)
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            color: Color::Red, // 新节点默认为红色
            left: None,
            right: None,
            size: 1,
        }
    }

    /// 创建黑色节点
    fn new_black(key: K, value: V) -> Self {
        Self {
            key,
            value,
            color: Color::Black,
            left: None,
            right: None,
            size: 1,
        }
    }

    /// 更新子树大小
    fn update_size(&mut self) {
        self.size = 1
            + self.left.as_ref().map_or(0, |n| n.size)
            + self.right.as_ref().map_or(0, |n| n.size);
    }

    /// 判断节点是否为红色
    fn is_red(&self) -> bool {
        self.color == Color::Red
    }
}

/// 红黑树结构体
#[derive(Debug)]
pub struct RedBlackTree<K: Ord + Debug, V: Debug> {
    root: Option<Box<Node<K, V>>>,
    size: usize,
}

impl<K: Ord + Debug, V: Debug> RedBlackTree<K, V> {
    /// 创建空的红黑树
    ///
    /// # 示例
    /// ```
    /// use algorithms::red_black_tree::RedBlackTree;
    /// let tree: RedBlackTree<i32, &str> = RedBlackTree::new();
    /// ```
    pub fn new() -> Self {
        Self {
            root: None,
            size: 0,
        }
    }

    /// 获取树中节点数量
    pub fn len(&self) -> usize {
        self.size
    }

    /// 判断树是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 左旋转
    ///
    /// ```text
    ///     x              y
    ///    / \            / \
    ///   a   y    =>    x   c
    ///      / \        / \
    ///     b   c      a   b
    /// ```
    fn rotate_left(mut h: Box<Node<K, V>>) -> Box<Node<K, V>> {
        let mut x = h.right.take().unwrap();
        h.right = x.left.take();
        h.update_size();
        
        x.left = Some(h);
        x.color = x.left.as_ref().unwrap().color;
        x.left.as_mut().unwrap().color = Color::Red;
        x.update_size();
        
        x
    }

    /// 右旋转
    ///
    /// ```text
    ///       y          x
    ///      / \        / \
    ///     x   c  =>  a   y
    ///    / \            / \
    ///   a   b          b   c
    /// ```
    fn rotate_right(mut h: Box<Node<K, V>>) -> Box<Node<K, V>> {
        let mut x = h.left.take().unwrap();
        h.left = x.right.take();
        h.update_size();
        
        x.right = Some(h);
        x.color = x.right.as_ref().unwrap().color;
        x.right.as_mut().unwrap().color = Color::Red;
        x.update_size();
        
        x
    }

    /// 颜色翻转
    ///
    /// 将红色节点的两个红色子节点翻转为黑色，节点本身变为红色
    fn flip_colors(h: &mut Box<Node<K, V>>) {
        h.color = Color::Red;
        if let Some(ref mut left) = h.left {
            left.color = Color::Black;
        }
        if let Some(ref mut right) = h.right {
            right.color = Color::Black;
        }
    }

    /// 判断节点的左子节点是否为红色
    fn is_red_left(h: &Box<Node<K, V>>) -> bool {
        h.left.as_ref().map_or(false, |n| n.is_red())
    }

    /// 判断节点的右子节点是否为红色
    fn is_red_right(h: &Box<Node<K, V>>) -> bool {
        h.right.as_ref().map_or(false, |n| n.is_red())
    }

    /// 插入键值对
    ///
    /// # 参数
    /// - `key`: 键
    /// - `value`: 值
    ///
    /// # 复杂度
    /// - 时间复杂度: O(log n)
    ///
    /// # 示例
    /// ```
    /// use algorithms::red_black_tree::RedBlackTree;
    /// let mut tree = RedBlackTree::new();
    /// tree.insert(5, "five");
    /// tree.insert(3, "three");
    /// ```
    pub fn insert(&mut self, key: K, value: V) {
        self.root = Some(Self::insert_recursive(self.root.take(), key, value));
        // 根节点必须是黑色
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        self.size += 1;
    }

    fn insert_recursive(
        h: Option<Box<Node<K, V>>>,
        key: K,
        value: V,
    ) -> Box<Node<K, V>> {
        match h {
            None => return Box::new(Node::new(key, value)),
            Some(mut h) => {
                // 处理4-节点(需要分裂)
                if Self::is_red_left(&h) && Self::is_red_right(&h) {
                    Self::flip_colors(&mut h);
                }

                match key.cmp(&h.key) {
                    Ordering::Less => {
                        h.left = Some(Self::insert_recursive(h.left.take(), key, value));
                    }
                    Ordering::Greater => {
                        h.right = Some(Self::insert_recursive(h.right.take(), key, value));
                    }
                    Ordering::Equal => {
                        h.value = value; // 更新值
                        self.size -= 1; // 不增加计数
                        return h;
                    }
                }

                h.update_size();

                // 修复右倾的红色链接
                if Self::is_red_right(&h) && !Self::is_red_left(&h) {
                    h = Self::rotate_left(h);
                }
                if Self::is_red_left(&h) {
                    if let Some(ref left) = h.left {
                        if left.left.as_ref().map_or(false, |n| n.is_red()) {
                            h = Self::rotate_right(h);
                        }
                    }
                }

                h
            }
        }
    }

    /// 查找键对应的值
    ///
    /// # 参数
    /// - `key`: 要查找的键
    ///
    /// # 返回
    /// - 如果找到，返回Some(&V)；否则返回None
    ///
    /// # 复杂度
    /// - 时间复杂度: O(log n)
    pub fn get(&self, key: &K) -> Option<&V> {
        Self::get_recursive(&self.root, key)
    }

    fn get_recursive(h: &Option<Box<Node<K, V>>>, key: &K) -> Option<&V> {
        match h {
            None => None,
            Some(h) => match key.cmp(&h.key) {
                Ordering::Less => Self::get_recursive(&h.left, key),
                Ordering::Greater => Self::get_recursive(&h.right, key),
                Ordering::Equal => Some(&h.value),
            },
        }
    }

    /// 判断树中是否包含指定键
    pub fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// 删除最小键
    ///
    /// # 复杂度
    /// - 时间复杂度: O(log n)
    pub fn remove_min(&mut self) -> Option<(K, V)> {
        if self.root.is_none() {
            return None;
        }
        
        self.root = Some(Self::move_red_left(self.root.take().unwrap()));
        let result = Self::remove_min_recursive(self.root.take());
        
        match result {
            (Some(node), min_pair) => {
                self.root = Some(Self::fix_up(node));
                if let Some(ref mut root) = self.root {
                    root.color = Color::Black;
                }
                self.size -= 1;
                min_pair
            }
            (None, min_pair) => {
                self.root = None;
                min_pair
            }
        }
    }

    fn remove_min_recursive(
        h: Option<Box<Node<K, V>>>,
    ) -> (Option<Box<Node<K, V>>>, Option<(K, V)>) {
        match h {
            None => (None, None),
            Some(mut h) => {
                if h.left.is_none() {
                    // 找到最小节点
                    return (None, Some((h.key, h.value)));
                }
                
                let (new_left, result) = Self::remove_min_recursive(h.left.take());
                h.left = new_left;
                h.update_size();
                (Some(Self::fix_up(h)), result)
            }
        }
    }

    fn move_red_left(mut h: Box<Node<K, V>>) -> Box<Node<K, V>> {
        Self::flip_colors(&mut h);
        if let Some(ref right) = h.right {
            if right.left.as_ref().map_or(false, |n| n.is_red()) {
                h.right = Some(Self::rotate_right(h.right.take().unwrap()));
                h = Self::rotate_left(h);
                Self::flip_colors(&mut h);
            }
        }
        h
    }

    fn move_red_right(mut h: Box<Node<K, V>>) -> Box<Node<K, V>> {
        Self::flip_colors(&mut h);
        if let Some(ref left) = h.left {
            if left.left.as_ref().map_or(false, |n| n.is_red()) {
                h = Self::rotate_right(h);
                Self::flip_colors(&mut h);
            }
        }
        h
    }

    fn fix_up(mut h: Box<Node<K, V>>) -> Box<Node<K, V>> {
        // 修复右倾的红色链接
        if Self::is_red_right(&h) {
            h = Self::rotate_left(h);
        }
        if Self::is_red_left(&h) {
            if let Some(ref left) = h.left {
                if left.left.as_ref().map_or(false, |n| n.is_red()) {
                    h = Self::rotate_right(h);
                }
            }
        }
        if Self::is_red_left(&h) && Self::is_red_right(&h) {
            Self::flip_colors(&mut h);
        }
        h.update_size();
        h
    }

    /// 删除指定键
    ///
    /// # 参数
    /// - `key`: 要删除的键
    ///
    /// # 返回
    /// - 如果删除成功，返回Some(值)；否则返回None
    ///
    /// # 复杂度
    /// - 时间复杂度: O(log n)
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if !self.contains(key) {
            return None;
        }

        self.root = Some(Self::move_red_left(self.root.take().unwrap()));
        let (new_root, result) = Self::remove_recursive(self.root.take(), key);
        
        self.root = new_root.map(Self::fix_up);
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        self.size -= 1;
        
        result
    }

    fn remove_recursive(
        h: Option<Box<Node<K, V>>>,
        key: &K,
    ) -> (Option<Box<Node<K, V>>>, Option<V>) {
        match h {
            None => (None, None),
            Some(mut h) => {
                match key.cmp(&h.key) {
                    Ordering::Less => {
                        let (new_left, result) = Self::remove_recursive(h.left.take(), key);
                        h.left = new_left;
                        h.update_size();
                        (Some(Self::fix_up(h)), result)
                    }
                    Ordering::Equal => {
                        // 找到要删除的节点
                        if h.right.is_none() {
                            return (h.left, Some(h.value));
                        }
                        
                        // 找到右子树的最小节点替代
                        let (new_right, min_pair) = Self::remove_min_recursive(h.right.take());
                        if let Some((min_key, min_value)) = min_pair {
                            let old_value = h.value;
                            h.key = min_key;
                            h.value = min_value;
                            h.right = new_right;
                            h.update_size();
                            (Some(Self::fix_up(h)), Some(old_value))
                        } else {
                            (Some(h), None)
                        }
                    }
                    Ordering::Greater => {
                        let (new_right, result) = Self::remove_recursive(h.right.take(), key);
                        h.right = new_right;
                        h.update_size();
                        (Some(Self::fix_up(h)), result)
                    }
                }
            }
        }
    }

    /// 获取最小键
    pub fn min(&self) -> Option<(&K, &V)> {
        Self::min_recursive(&self.root)
    }

    fn min_recursive(h: &Option<Box<Node<K, V>>>) -> Option<(&K, &V)> {
        match h {
            None => None,
            Some(h) => {
                if h.left.is_none() {
                    Some((&h.key, &h.value))
                } else {
                    Self::min_recursive(&h.left)
                }
            }
        }
    }

    /// 获取最大键
    pub fn max(&self) -> Option<(&K, &V)> {
        Self::max_recursive(&self.root)
    }

    fn max_recursive(h: &Option<Box<Node<K, V>>>) -> Option<(&K, &V)> {
        match h {
            None => None,
            Some(h) => {
                if h.right.is_none() {
                    Some((&h.key, &h.value))
                } else {
                    Self::max_recursive(&h.right)
                }
            }
        }
    }

    /// 中序遍历获取排序后的键值对
    pub fn to_vec(&self) -> Vec<(&K, &V)> {
        let mut result = Vec::with_capacity(self.size);
        Self::inorder_recursive(&self.root, &mut result);
        result
    }

    fn inorder_recursive<'a>(
        h: &'a Option<Box<Node<K, V>>>,
        result: &mut Vec<(&'a K, &'a V)>,
    ) {
        if let Some(h) = h {
            Self::inorder_recursive(&h.left, result);
            result.push((&h.key, &h.value));
            Self::inorder_recursive(&h.right, result);
        }
    }

    /// 验证红黑树性质(用于测试)
    #[cfg(test)]
    fn validate(&self) -> bool {
        if self.root.is_none() {
            return true;
        }
        // 根节点必须是黑色
        if self.root.as_ref().unwrap().is_red() {
            return false;
        }
        let (valid, _) = Self::validate_recursive(&self.root);
        valid
    }

    #[cfg(test)]
    fn validate_recursive(h: &Option<Box<Node<K, V>>>) -> (bool, usize) {
        match h {
            None => (true, 1), // NIL节点算一个黑色节点
            Some(h) => {
                // 红色节点的子节点必须是黑色
                if h.is_red() {
                    if Self::is_red_left(h) || Self::is_red_right(h) {
                        return (false, 0);
                    }
                }

                let (left_valid, left_black) = Self::validate_recursive(&h.left);
                let (right_valid, right_black) = Self::validate_recursive(&h.right);

                // 左右子树的黑色节点数必须相同
                if !left_valid || !right_valid || left_black != right_black {
                    return (false, 0);
                }

                let black_count = left_black + if h.color == Color::Black { 1 } else { 0 };
                (true, black_count)
            }
        }
    }
}

impl<K: Ord + Debug, V: Debug> Default for RedBlackTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_insert_and_get() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        
        assert_eq!(tree.get(&5), Some(&"five"));
        assert_eq!(tree.get(&3), Some(&"three"));
        assert_eq!(tree.get(&7), Some(&"seven"));
        assert_eq!(tree.get(&10), None);
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "original");
        tree.insert(5, "updated");
        
        assert_eq!(tree.get(&5), Some(&"updated"));
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_contains() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(1, "one");
        tree.insert(2, "two");
        
        assert!(tree.contains(&1));
        assert!(tree.contains(&2));
        assert!(!tree.contains(&3));
    }

    #[test]
    fn test_min_max() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        tree.insert(1, "one");
        tree.insert(9, "nine");
        
        assert_eq!(tree.min(), Some((&1, &"one")));
        assert_eq!(tree.max(), Some((&9, &"nine")));
    }

    #[test]
    fn test_to_vec() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        tree.insert(1, "one");
        
        let vec = tree.to_vec();
        assert_eq!(vec, vec![(&1, &"one"), (&3, &"three"), (&5, &"five"), (&7, &"seven")]);
    }

    #[test]
    fn test_remove() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        
        assert_eq!(tree.remove(&3), Some("three"));
        assert_eq!(tree.get(&3), None);
        assert_eq!(tree.len(), 2);
        
        assert_eq!(tree.remove(&10), None);
    }

    #[test]
    fn test_remove_root() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        
        assert_eq!(tree.remove(&5), Some("five"));
        assert!(!tree.contains(&5));
        assert!(tree.validate());
    }

    #[test]
    fn test_remove_all() {
        let mut tree = RedBlackTree::new();
        
        for i in 0..10 {
            tree.insert(i, i.to_string());
        }
        
        for i in 0..10 {
            assert!(tree.validate());
            assert_eq!(tree.remove(&i), Some(i.to_string()));
        }
        
        assert!(tree.is_empty());
    }

    #[test]
    fn test_remove_min() {
        let mut tree = RedBlackTree::new();
        
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.insert(7, "seven");
        
        assert_eq!(tree.remove_min(), Some((3, "three")));
        assert_eq!(tree.min(), Some((&5, &"five")));
    }

    #[test]
    fn test_large_tree() {
        let mut tree = RedBlackTree::new();
        
        // 插入1000个元素
        for i in 0..1000 {
            tree.insert(i, i * 2);
        }
        
        assert_eq!(tree.len(), 1000);
        assert!(tree.validate());
        
        // 查找
        for i in 0..1000 {
            assert_eq!(tree.get(&i), Some(&(i * 2)));
        }
        
        // 删除一半
        for i in 0..500 {
            assert_eq!(tree.remove(&i), Some(i * 2));
            assert!(tree.validate());
        }
        
        assert_eq!(tree.len(), 500);
    }

    #[test]
    fn test_rb_properties() {
        let mut tree = RedBlackTree::new();
        
        for i in 0..100 {
            tree.insert(i, i);
            assert!(tree.validate(), "Tree invalid after inserting {}", i);
        }
    }

    #[test]
    fn test_empty_tree() {
        let tree: RedBlackTree<i32, &str> = RedBlackTree::new();
        
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert!(tree.to_vec().is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut tree = RedBlackTree::new();
        tree.insert(42, "answer");
        
        assert_eq!(tree.len(), 1);
        assert_eq!(tree.min(), tree.max());
        assert!(tree.validate());
    }

    #[test]
    fn test_string_keys() {
        let mut tree = RedBlackTree::new();
        
        tree.insert("banana", 1);
        tree.insert("apple", 2);
        tree.insert("cherry", 3);
        
        let vec = tree.to_vec();
        assert_eq!(vec[0].0, &"apple");
        assert_eq!(vec[1].0, &"banana");
        assert_eq!(vec[2].0, &"cherry");
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 基本用法
    pub fn example_basic() {
        println!("=== 红黑树基本用法 ===");
        
        let mut scores = RedBlackTree::new();
        
        // 插入学生成绩
        scores.insert("Alice", 85);
        scores.insert("Bob", 92);
        scores.insert("Charlie", 78);
        scores.insert("Diana", 95);
        
        println!("学生成绩:");
        for (name, score) in scores.to_vec() {
            println!("  {}: {}", name, score);
        }
        
        // 查找
        if let Some(score) = scores.get(&"Bob") {
            println!("\nBob的成绩是: {}", score);
        }
        
        // 更新
        scores.insert("Bob", 95);
        println!("Bob更新后的成绩: {}", scores.get(&"Bob").unwrap());
    }

    /// 示例2: 有序统计
    pub fn example_order_statistics() {
        println!("\n=== 有序统计示例 ===");
        
        let mut tree = RedBlackTree::new();
        
        for i in vec![50, 30, 70, 20, 40, 60, 80] {
            tree.insert(i, format!("value-{}", i));
        }
        
        println!("有序遍历:");
        for (k, v) in tree.to_vec() {
            println!("  {} -> {}", k, v);
        }
        
        println!("\n最小值: {:?}", tree.min());
        println!("最大值: {:?}", tree.max());
    }

    /// 示例3: 作为集合使用
    pub fn example_as_set() {
        println!("\n=== 集合操作示例 ===");
        
        let mut set = RedBlackTree::new();
        
        // 添加元素
        let elements = vec![5, 2, 8, 1, 9, 3];
        for &x in &elements {
            set.insert(x, ());
        }
        
        println!("集合元素 (有序):");
        for (k, _) in set.to_vec() {
            print!("{} ", k);
        }
        println!();
        
        // 检查存在性
        println!("\n集合包含 3? {}", set.contains(&3));
        println!("集合包含 7? {}", set.contains(&7));
        
        // 删除元素
        set.remove(&2);
        println!("删除2后，集合包含 2? {}", set.contains(&2));
    }
}
