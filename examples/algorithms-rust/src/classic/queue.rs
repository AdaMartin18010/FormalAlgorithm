//! # 队列 (Queue)
//!
//! 先进先出 (FIFO) 的线性数据结构。
//!
//! ## 核心思想
//! - 在队尾（rear/tail）进行入队（enqueue），在队头（front/head）进行出队（dequeue）
//! - 典型应用：任务调度、缓冲区、广度优先搜索（BFS）
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | enqueue | O(1) 均摊 | O(1) |
//! | dequeue | O(1) | O(1) |
//! | peek | O(1) | O(1) |

use std::ptr::NonNull;

/// 队列节点
struct QueueNode<T> {
    value: T,
    next: Option<NonNull<QueueNode<T>>>,
}

/// 基于链表实现的队列
///
/// # 示例
/// ```
/// use formal_algorithms::queue::Queue;
///
/// let mut queue = Queue::new();
/// queue.enqueue(1);
/// queue.enqueue(2);
/// assert_eq!(queue.dequeue(), Some(1));
/// assert_eq!(queue.peek(), Some(&2));
/// ```
pub struct Queue<T> {
    head: Option<NonNull<QueueNode<T>>>,
    tail: Option<NonNull<QueueNode<T>>>,
    len: usize,
}

unsafe impl<T: Send> Send for Queue<T> {}
unsafe impl<T: Sync> Sync for Queue<T> {}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Queue<T> {
    /// 创建空队列
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// 入队
    pub fn enqueue(&mut self, value: T) {
        let new_node = Box::new(QueueNode { value, next: None });
        let node_ptr = NonNull::new(Box::into_raw(new_node)).unwrap();

        unsafe {
            if let Some(tail) = self.tail {
                (*tail.as_ptr()).next = Some(node_ptr);
            } else {
                self.head = Some(node_ptr);
            }
        }
        self.tail = Some(node_ptr);
        self.len += 1;
    }

    /// 出队
    pub fn dequeue(&mut self) -> Option<T> {
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;
            if self.head.is_none() {
                self.tail = None;
            }
            self.len -= 1;
            node.value
        })
    }

    /// 查看队头元素
    pub fn peek(&self) -> Option<&T> {
        self.head.map(|node| unsafe { &(*node.as_ptr()).value })
    }

    /// 查看队头元素的可变引用
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.map(|node| unsafe { &mut (*node.as_ptr()).value })
    }

    /// 返回队列长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 清空队列
    pub fn clear(&mut self) {
        while self.dequeue().is_some() {}
    }
}

impl<T> Drop for Queue<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

/// 基于两个栈实现的队列（amortized O(1)）
///
/// # 示例
/// ```
/// use formal_algorithms::queue::QueueWithTwoStacks;
///
/// let mut queue = QueueWithTwoStacks::new();
/// queue.enqueue(1);
/// queue.enqueue(2);
/// assert_eq!(queue.dequeue(), Some(1));
/// assert_eq!(queue.dequeue(), Some(2));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueueWithTwoStacks<T> {
    in_stack: Vec<T>,
    out_stack: Vec<T>,
}

impl<T> Default for QueueWithTwoStacks<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> QueueWithTwoStacks<T> {
    /// 创建空队列
    pub fn new() -> Self {
        Self {
            in_stack: Vec::new(),
            out_stack: Vec::new(),
        }
    }

    /// 入队
    pub fn enqueue(&mut self, value: T) {
        self.in_stack.push(value);
    }

    /// 出队
    pub fn dequeue(&mut self) -> Option<T> {
        if self.out_stack.is_empty() {
            while let Some(v) = self.in_stack.pop() {
                self.out_stack.push(v);
            }
        }
        self.out_stack.pop()
    }

    /// 查看队头元素
    pub fn peek(&self) -> Option<&T> {
        if self.out_stack.is_empty() {
            self.in_stack.first()
        } else {
            self.out_stack.last()
        }
    }

    /// 返回长度
    pub fn len(&self) -> usize {
        self.in_stack.len() + self.out_stack.len()
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.in_stack.is_empty() && self.out_stack.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_queue_basic() {
        let mut queue = Queue::new();
        queue.enqueue(1);
        queue.enqueue(2);
        queue.enqueue(3);
        assert_eq!(queue.len(), 3);
        assert_eq!(queue.peek(), Some(&1));
        assert_eq!(queue.dequeue(), Some(1));
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.dequeue(), Some(3));
        assert_eq!(queue.dequeue(), None);
    }

    #[test]
    fn test_queue_clear() {
        let mut queue = Queue::new();
        queue.enqueue(1);
        queue.enqueue(2);
        queue.clear();
        assert!(queue.is_empty());
        assert_eq!(queue.dequeue(), None);
    }

    #[test]
    fn test_queue_two_stacks() {
        let mut queue = QueueWithTwoStacks::new();
        queue.enqueue(1);
        queue.enqueue(2);
        queue.enqueue(3);
        assert_eq!(queue.dequeue(), Some(1));
        queue.enqueue(4);
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.dequeue(), Some(3));
        assert_eq!(queue.dequeue(), Some(4));
        assert_eq!(queue.dequeue(), None);
    }
}
