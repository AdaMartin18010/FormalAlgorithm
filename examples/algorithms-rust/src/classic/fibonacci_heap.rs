//! 斐波那契堆（Fibonacci Heap）
//!
//! 对标：CLRS 第4版 Chapter 19
//!
//! 斐波那契堆是一种可合并堆，在均摊意义下支持最优时间复杂度：
//! - `insert`: O(1)
//! - `extract_min`: O(log n) 均摊
//! - `decrease_key`: O(1) 均摊
//! - `union`: O(1)
//!
//! 由于 `decrease_key` 的常数均摊代价，斐波那契堆是 Dijkstra 和 Prim 算法的理论最优数据结构。

use std::ptr::NonNull;

/// 斐波那契堆节点
///
/// 使用裸指针构建双向循环链表，节点可能被多个指针引用（根链表、子链表）。
#[derive(Debug)]
pub struct Node<T: Ord> {
    key: T,
    degree: usize,
    mark: bool,
    parent: Option<NonNull<Node<T>>>,
    child: Option<NonNull<Node<T>>>,
    left: Option<NonNull<Node<T>>>,
    right: Option<NonNull<Node<T>>>,
}

impl<T: Ord + Clone> Node<T> {
    fn new(key: T) -> NonNull<Node<T>> {
        let node = Box::into_raw(Box::new(Node {
            key,
            degree: 0,
            mark: false,
            parent: None,
            child: None,
            left: None,
            right: None,
        }));
        unsafe {
            (*node).left = Some(NonNull::new_unchecked(node));
            (*node).right = Some(NonNull::new_unchecked(node));
        }
        unsafe { NonNull::new_unchecked(node) }
    }

    unsafe fn key(&self) -> &T {
        &self.key
    }

    unsafe fn key_mut(&mut self) -> &mut T {
        &mut self.key
    }
}

/// 节点句柄，用于 `decrease_key`
///
/// # Safety
/// 句柄指向的节点必须始终属于创建它的斐波那契堆，且在堆被释放前有效。
#[derive(Debug, Clone, Copy)]
pub struct NodeHandle<T: Ord>(NonNull<Node<T>>);

impl<T: Ord + Clone> NodeHandle<T> {
    /// 获取节点当前的键值引用
    ///
    /// # Safety
    /// 仅在句柄对应的堆仍然存活时安全调用。
    pub unsafe fn key(&self) -> &T {
        self.0.as_ref().key()
    }
}

/// 斐波那契堆
#[derive(Debug)]
pub struct FibonacciHeap<T: Ord + Clone> {
    min: Option<NonNull<Node<T>>>,
    n: usize,
}

impl<T: Ord + Clone> FibonacciHeap<T> {
    /// 创建空斐波那契堆
    pub fn new() -> Self {
        Self { min: None, n: 0 }
    }

    /// 插入元素，返回节点句柄
    pub fn insert(&mut self, key: T) -> NodeHandle<T> {
        let node = Node::new(key);
        if let Some(min) = self.min {
            unsafe {
                Self::list_insert(min, node);
                if node.as_ref().key < min.as_ref().key {
                    self.min = Some(node);
                }
            }
        } else {
            self.min = Some(node);
        }
        self.n += 1;
        NodeHandle(node)
    }

    /// 查看最小元素
    pub fn peek_min(&self) -> Option<&T> {
        self.min.map(|min| unsafe { min.as_ref().key() })
    }

    /// 提取最小元素
    ///
    /// 时间复杂度：O(log n) 均摊
    pub fn extract_min(&mut self) -> Option<T> {
        let min = self.min?;
        unsafe {
            if let Some(child) = min.as_ref().child {
                let mut current = child;
                loop {
                    current.as_mut().parent = None;
                    current = current.as_ref().right.unwrap();
                    if current == child {
                        break;
                    }
                }
                Self::list_merge(min, child);
            }

            let min_right = min.as_ref().right.unwrap();
            Self::list_remove(min);

            if min == min_right {
                self.min = None;
            } else {
                self.min = Some(min_right);
                self.consolidate();
            }
        }

        self.n -= 1;
        let key = unsafe { Box::from_raw(min.as_ptr()).key };
        Some(key)
    }

    /// 关键字减值
    ///
    /// 时间复杂度：O(1) 均摊
    ///
    /// # Panics
    /// 若 `new_key` 大于当前键值则 panic。
    pub fn decrease_key(&mut self, handle: NodeHandle<T>, new_key: T) {
        unsafe {
            let mut node = handle.0;
            assert!(
                new_key <= *node.as_ref().key(),
                "new_key must be <= current key"
            );
            *node.as_mut().key_mut() = new_key.clone();

            if let Some(parent) = node.as_ref().parent {
                if new_key < parent.as_ref().key {
                    self.cut(node, parent);
                    self.cascading_cut(parent);
                }
            }

            if new_key < self.min.unwrap().as_ref().key {
                self.min = Some(node);
            }
        }
    }

    /// 合并两个斐波那契堆
    ///
    /// 时间复杂度：O(1)
    pub fn union(&mut self, mut other: FibonacciHeap<T>) -> FibonacciHeap<T> {
        if self.min.is_none() {
            *self = other;
            return FibonacciHeap::new();
        }
        if other.min.is_none() {
            return FibonacciHeap::new();
        }

        unsafe {
            let min1 = self.min.unwrap();
            let min2 = other.min.unwrap();
            Self::list_merge(min1, min2);
            if min2.as_ref().key < min1.as_ref().key {
                self.min = Some(min2);
            }
        }

        self.n += other.n;
        other.min = None;
        other.n = 0;
        FibonacciHeap::new()
    }

    /// 返回元素数量
    pub fn len(&self) -> usize {
        self.n
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    // ========== 内部辅助方法 ==========

    /// 将 `node` 插入到 `list` 的双向循环链表中（插在 list 的左边）
    unsafe fn list_insert(mut list: NonNull<Node<T>>, mut node: NonNull<Node<T>>) {
        let mut left = list.as_ref().left.unwrap();
        node.as_mut().left = Some(left);
        node.as_mut().right = Some(list);
        left.as_mut().right = Some(node);
        list.as_mut().left = Some(node);
    }

    /// 从双向循环链表中移除单个节点
    unsafe fn list_remove(mut node: NonNull<Node<T>>) {
        let mut left = node.as_ref().left.unwrap();
        let mut right = node.as_ref().right.unwrap();
        left.as_mut().right = Some(right);
        right.as_mut().left = Some(left);
        node.as_mut().left = Some(node);
        node.as_mut().right = Some(node);
    }

    /// 合并两个双向循环链表（以 root1 和 root2 为代表节点）
    unsafe fn list_merge(mut root1: NonNull<Node<T>>, mut root2: NonNull<Node<T>>) {
        let mut r1_left = root1.as_ref().left.unwrap();
        let mut r2_left = root2.as_ref().left.unwrap();
        r1_left.as_mut().right = Some(root2);
        root2.as_mut().left = Some(r1_left);
        r2_left.as_mut().right = Some(root1);
        root1.as_mut().left = Some(r2_left);
    }

    /// 合并（consolidate）根链表，使得没有两棵树的度数相同
    unsafe fn consolidate(&mut self) {
        let max_degree = (self.n as f64).log2().ceil() as usize + 1;
        let mut degree_table: Vec<Option<NonNull<Node<T>>>> = vec![None; max_degree + 1];

        let mut roots = Vec::new();
        if let Some(start) = self.min {
            let mut current = start;
            loop {
                roots.push(current);
                current = current.as_ref().right.unwrap();
                if current == start {
                    break;
                }
            }
        }

        for mut x in roots {
            let mut d = x.as_ref().degree;
            while let Some(mut y) = degree_table[d] {
                if x.as_ref().key > y.as_ref().key {
                    std::mem::swap(&mut x, &mut y);
                }
                self.link(y, x);
                degree_table[d] = None;
                d += 1;
            }
            degree_table[d] = Some(x);
        }

        self.min = None;
        for node in degree_table.into_iter().flatten() {
            if let Some(min) = self.min {
                if node.as_ref().key < min.as_ref().key {
                    self.min = Some(node);
                }
            } else {
                self.min = Some(node);
            }
        }
    }

    /// 将 y 作为 x 的子节点链接起来（y 的度数在此之前必定为 0）
    unsafe fn link(&mut self, mut y: NonNull<Node<T>>, mut x: NonNull<Node<T>>) {
        Self::list_remove(y);
        y.as_mut().parent = Some(x);
        y.as_mut().mark = false;

        if let Some(child) = x.as_ref().child {
            Self::list_insert(child, y);
        } else {
            x.as_mut().child = Some(y);
            y.as_mut().left = Some(y);
            y.as_mut().right = Some(y);
        }
        x.as_mut().degree += 1;
    }

    /// 剪切：将 node 从其父节点处切下，移入根链表
    unsafe fn cut(&mut self, mut node: NonNull<Node<T>>, mut parent: NonNull<Node<T>>) {
        Self::list_remove(node);
        if let Some(child) = parent.as_ref().child {
            if child == node {
                let right = node.as_ref().right.unwrap();
                parent.as_mut().child = if right == node { None } else { Some(right) };
            }
        }
        parent.as_mut().degree -= 1;
        node.as_mut().parent = None;
        node.as_mut().mark = false;

        let min = self.min.unwrap();
        Self::list_insert(min, node);
    }

    /// 级联剪切
    unsafe fn cascading_cut(&mut self, mut node: NonNull<Node<T>>) {
        if let Some(parent) = node.as_ref().parent {
            if !node.as_ref().mark {
                node.as_mut().mark = true;
            } else {
                self.cut(node, parent);
                self.cascading_cut(parent);
            }
        }
    }
}

impl<T: Ord + Clone> Default for FibonacciHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_insert_and_peek() {
        let mut heap = FibonacciHeap::new();
        assert!(heap.is_empty());
        heap.insert(3);
        heap.insert(1);
        heap.insert(2);
        assert_eq!(heap.peek_min(), Some(&1));
        assert_eq!(heap.len(), 3);
    }

    #[test]
    fn test_extract_min_ordering() {
        let mut heap = FibonacciHeap::new();
        let values = vec![5, 2, 8, 1, 9, 3];
        for v in values {
            heap.insert(v);
        }
        let mut extracted = Vec::new();
        while let Some(min) = heap.extract_min() {
            extracted.push(min);
        }
        assert_eq!(extracted, vec![1, 2, 3, 5, 8, 9]);
        assert!(heap.is_empty());
    }

    #[test]
    fn test_decrease_key() {
        let mut heap = FibonacciHeap::new();
        let h10 = heap.insert(10);
        let h20 = heap.insert(20);
        heap.insert(5);

        heap.decrease_key(h10, 2);
        assert_eq!(heap.peek_min(), Some(&2));

        heap.decrease_key(h20, 1);
        assert_eq!(heap.peek_min(), Some(&1));
    }

    #[test]
    fn test_union() {
        let mut h1 = FibonacciHeap::new();
        h1.insert(1);
        h1.insert(5);

        let mut h2 = FibonacciHeap::new();
        h2.insert(2);
        h2.insert(3);

        h1.union(h2);
        assert_eq!(h1.extract_min(), Some(1));
        assert_eq!(h1.extract_min(), Some(2));
        assert_eq!(h1.extract_min(), Some(3));
        assert_eq!(h1.extract_min(), Some(5));
    }

    #[test]
    fn test_duplicate_keys() {
        let mut heap = FibonacciHeap::new();
        heap.insert(5);
        heap.insert(5);
        heap.insert(5);
        assert_eq!(heap.len(), 3);
        assert_eq!(heap.extract_min(), Some(5));
        assert_eq!(heap.extract_min(), Some(5));
        assert_eq!(heap.extract_min(), Some(5));
    }
}
