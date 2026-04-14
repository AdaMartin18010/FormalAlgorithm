//! # 双端队列 (Deque)
//!
//! 允许在队列两端进行插入和删除的线性数据结构。
//!
//! ## 核心思想
//! - 在头部和尾部均支持 O(1) 的 push/pop 操作
//! - 可作为栈或队列的泛化形式
//! - 典型应用：滑动窗口最大值、回文检查、任务窃取（work stealing）
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | push_front | O(1) | O(1) |
//! | push_back | O(1) | O(1) |
//! | pop_front | O(1) | O(1) |
//! | pop_back | O(1) | O(1) |
//! | peek_front/back | O(1) | O(1) |

use std::ptr::NonNull;

/// 双端队列节点
struct DequeNode<T> {
    value: T,
    prev: Option<NonNull<DequeNode<T>>>,
    next: Option<NonNull<DequeNode<T>>>,
}

/// 基于双向链表实现的双端队列
///
/// # 示例
/// ```
/// use formal_algorithms::deque::Deque;
///
/// let mut deque = Deque::new();
/// deque.push_back(1);
/// deque.push_back(2);
/// deque.push_front(0);
/// assert_eq!(deque.pop_front(), Some(0));
/// assert_eq!(deque.pop_back(), Some(2));
/// assert_eq!(deque.peek_front(), Some(&1));
/// ```
pub struct Deque<T> {
    head: Option<NonNull<DequeNode<T>>>,
    tail: Option<NonNull<DequeNode<T>>>,
    len: usize,
}

unsafe impl<T: Send> Send for Deque<T> {}
unsafe impl<T: Sync> Sync for Deque<T> {}

impl<T> Default for Deque<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Deque<T> {
    /// 创建空双端队列
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// 在头部插入元素
    pub fn push_front(&mut self, value: T) {
        let new_node = Box::new(DequeNode {
            value,
            prev: None,
            next: self.head,
        });
        let node_ptr = NonNull::new(Box::into_raw(new_node)).unwrap();

        unsafe {
            if let Some(old_head) = self.head {
                (*old_head.as_ptr()).prev = Some(node_ptr);
            } else {
                self.tail = Some(node_ptr);
            }
        }
        self.head = Some(node_ptr);
        self.len += 1;
    }

    /// 在尾部插入元素
    pub fn push_back(&mut self, value: T) {
        let new_node = Box::new(DequeNode {
            value,
            prev: self.tail,
            next: None,
        });
        let node_ptr = NonNull::new(Box::into_raw(new_node)).unwrap();

        unsafe {
            if let Some(old_tail) = self.tail {
                (*old_tail.as_ptr()).next = Some(node_ptr);
            } else {
                self.head = Some(node_ptr);
            }
        }
        self.tail = Some(node_ptr);
        self.len += 1;
    }

    /// 移除并返回头部元素
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;
            if let Some(new_head) = self.head {
                (*new_head.as_ptr()).prev = None;
            } else {
                self.tail = None;
            }
            self.len -= 1;
            node.value
        })
    }

    /// 移除并返回尾部元素
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.tail = node.prev;
            if let Some(new_tail) = self.tail {
                (*new_tail.as_ptr()).next = None;
            } else {
                self.head = None;
            }
            self.len -= 1;
            node.value
        })
    }

    /// 查看头部元素
    pub fn peek_front(&self) -> Option<&T> {
        self.head.map(|node| unsafe { &(*node.as_ptr()).value })
    }

    /// 查看尾部元素
    pub fn peek_back(&self) -> Option<&T> {
        self.tail.map(|node| unsafe { &(*node.as_ptr()).value })
    }

    /// 返回队列长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 清空双端队列
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }
}

impl<T> Drop for Deque<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

/// 检查字符串是否为回文（使用双端队列）
///
/// # 示例
/// ```
/// use formal_algorithms::deque::is_palindrome;
///
/// assert!(is_palindrome("racecar"));
/// assert!(is_palindrome(""));
/// assert!(!is_palindrome("hello"));
/// ```
pub fn is_palindrome(s: &str) -> bool {
    let mut deque = Deque::new();
    for ch in s.chars() {
        deque.push_back(ch);
    }
    while deque.len() > 1 {
        if deque.pop_front() != deque.pop_back() {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deque_basic() {
        let mut deque = Deque::new();
        deque.push_back(1);
        deque.push_back(2);
        deque.push_front(0);
        assert_eq!(deque.len(), 3);
        assert_eq!(deque.peek_front(), Some(&0));
        assert_eq!(deque.peek_back(), Some(&2));
        assert_eq!(deque.pop_front(), Some(0));
        assert_eq!(deque.pop_back(), Some(2));
        assert_eq!(deque.pop_front(), Some(1));
        assert!(deque.is_empty());
    }

    #[test]
    fn test_deque_alternating() {
        let mut deque = Deque::new();
        for i in 0..100 {
            if i % 2 == 0 {
                deque.push_front(i);
            } else {
                deque.push_back(i);
            }
        }
        assert_eq!(deque.len(), 100);
        deque.clear();
        assert!(deque.is_empty());
    }

    #[test]
    fn test_is_palindrome() {
        assert!(is_palindrome("racecar"));
        assert!(is_palindrome(""));
        assert!(is_palindrome("a"));
        assert!(!is_palindrome("hello"));
        assert!(!is_palindrome("ab"));
    }
}
