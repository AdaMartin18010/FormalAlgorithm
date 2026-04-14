//! # 链表 (Linked List)
//!
//! 提供单链表、双向链表、循环链表三种基础实现。
//!
//! ## 核心思想
//! - **单链表**：每个节点仅保存指向下一节点的指针，适合顺序遍历与头插
//! - **双向链表**：每个节点保存前驱与后继指针，支持 O(1) 双向遍历与删除
//! - **循环链表**：尾节点指向头节点，形成环，适合轮询调度场景
//!
//! ## 复杂度分析
//! | 操作 | 单链表 | 双向链表 | 循环链表 |
//! |------|--------|----------|----------|
//! | 头插 | O(1) | O(1) | O(1) |
//! | 尾插 | O(n) | O(1)* | O(1)* |
//! | 删除(已知节点) | O(n) | O(1) | O(1) |
//! | 查找 | O(n) | O(n) | O(n) |

use std::ptr::NonNull;

// ==================== Singly Linked List ====================

/// 单链表节点
struct SllNode<T> {
    value: T,
    next: Option<Box<SllNode<T>>>,
}

/// 单链表
///
/// # 示例
/// ```
/// use formal_algorithms::linked_list::SinglyLinkedList;
///
/// let mut list = SinglyLinkedList::new();
/// list.push_front(1);
/// list.push_front(2);
/// assert_eq!(list.pop_front(), Some(2));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinglyLinkedList<T> {
    head: Option<Box<SllNode<T>>>,
    len: usize,
}

impl<T> Default for SinglyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> SinglyLinkedList<T> {
    /// 创建空单链表
    pub fn new() -> Self {
        Self { head: None, len: 0 }
    }

    /// 在头部插入元素，O(1)
    pub fn push_front(&mut self, value: T) {
        let new_node = Box::new(SllNode {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
        self.len += 1;
    }

    /// 移除并返回头部元素，O(1)
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            self.len -= 1;
            node.value
        })
    }

    /// 查看头部元素
    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.value)
    }

    /// 返回链表长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 查找元素并返回引用
    pub fn find(&self, value: &T) -> Option<&T>
    where
        T: PartialEq,
    {
        let mut current = self.head.as_deref();
        while let Some(node) = current {
            if &node.value == value {
                return Some(&node.value);
            }
            current = node.next.as_deref();
        }
        None
    }
}

// ==================== Doubly Linked List ====================

/// 双向链表节点
struct DllNode<T> {
    value: T,
    prev: Option<NonNull<DllNode<T>>>,
    next: Option<NonNull<DllNode<T>>>,
}

/// 双向链表
///
/// # 示例
/// ```
/// use formal_algorithms::linked_list::DoublyLinkedList;
///
/// let mut list = DoublyLinkedList::new();
/// list.push_back(1);
/// list.push_back(2);
/// list.push_front(0);
/// assert_eq!(list.pop_front(), Some(0));
/// assert_eq!(list.pop_back(), Some(2));
/// ```
pub struct DoublyLinkedList<T> {
    head: Option<NonNull<DllNode<T>>>,
    tail: Option<NonNull<DllNode<T>>>,
    len: usize,
}

unsafe impl<T: Send> Send for DoublyLinkedList<T> {}
unsafe impl<T: Sync> Sync for DoublyLinkedList<T> {}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DoublyLinkedList<T> {
    /// 创建空双向链表
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// 在头部插入元素，O(1)
    pub fn push_front(&mut self, value: T) {
        let new_node = Box::new(DllNode {
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

    /// 在尾部插入元素，O(1)
    pub fn push_back(&mut self, value: T) {
        let new_node = Box::new(DllNode {
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

    /// 移除并返回头部元素，O(1)
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

    /// 移除并返回尾部元素，O(1)
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

    /// 返回长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Drop for DoublyLinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

// ==================== Circular Linked List ====================

/// 循环链表节点
struct CllNode<T> {
    value: T,
    next: Option<NonNull<CllNode<T>>>,
}

/// 循环链表（单向循环）
///
/// # 示例
/// ```
/// use formal_algorithms::linked_list::CircularLinkedList;
///
/// let mut list = CircularLinkedList::new();
/// list.push(1);
/// list.push(2);
/// assert_eq!(list.rotate(), Some(&1));
/// assert_eq!(list.rotate(), Some(&2));
/// ```
pub struct CircularLinkedList<T> {
    tail: Option<NonNull<CllNode<T>>>,
    len: usize,
}

unsafe impl<T: Send> Send for CircularLinkedList<T> {}
unsafe impl<T: Sync> Sync for CircularLinkedList<T> {}

impl<T> Default for CircularLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> CircularLinkedList<T> {
    /// 创建空循环链表
    pub fn new() -> Self {
        Self { tail: None, len: 0 }
    }

    /// 在尾部插入元素（即 head 之前），O(1)
    pub fn push(&mut self, value: T) {
        let new_node = Box::new(CllNode { value, next: None });
        let node_ptr = NonNull::new(Box::into_raw(new_node)).unwrap();

        unsafe {
            if let Some(tail) = self.tail {
                let head = (*tail.as_ptr()).next;
                (*tail.as_ptr()).next = Some(node_ptr);
                (*node_ptr.as_ptr()).next = head;
                self.tail = Some(node_ptr);
            } else {
                (*node_ptr.as_ptr()).next = Some(node_ptr);
                self.tail = Some(node_ptr);
            }
        }
        self.len += 1;
    }

    /// 移除并返回头部元素，O(1)
    pub fn pop(&mut self) -> Option<T> {
        self.tail.map(|tail| unsafe {
            let head = (*tail.as_ptr()).next.unwrap();
            if head == tail {
                self.tail = None;
            } else {
                (*tail.as_ptr()).next = (*head.as_ptr()).next;
            }
            self.len -= 1;
            let node = Box::from_raw(head.as_ptr());
            node.value
        })
    }

    /// 轮询：将头节点移到尾部并返回其值引用，O(1)
    pub fn rotate(&mut self) -> Option<&T> {
        self.tail.map(|tail| unsafe {
            let head = (*tail.as_ptr()).next.unwrap();
            self.tail = Some(head);
            &(*head.as_ptr()).value
        })
    }

    /// 查看当前头部元素
    pub fn peek(&self) -> Option<&T> {
        self.tail.map(|tail| unsafe {
            let head = (*tail.as_ptr()).next.unwrap();
            &(*head.as_ptr()).value
        })
    }

    /// 返回长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Drop for CircularLinkedList<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singly_linked_list() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(2));
        assert_eq!(list.find(&1), Some(&1));
        assert_eq!(list.find(&99), None);
    }

    #[test]
    fn test_doubly_linked_list() {
        let mut list = DoublyLinkedList::new();
        list.push_back(1);
        list.push_back(2);
        list.push_front(0);
        assert_eq!(list.peek_front(), Some(&0));
        assert_eq!(list.peek_back(), Some(&2));
        assert_eq!(list.pop_front(), Some(0));
        assert_eq!(list.pop_back(), Some(2));
        assert_eq!(list.pop_front(), Some(1));
        assert!(list.is_empty());
    }

    #[test]
    fn test_circular_linked_list() {
        let mut list = CircularLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);
        assert_eq!(list.peek(), Some(&1));
        assert_eq!(list.rotate(), Some(&1));
        assert_eq!(list.peek(), Some(&2));
        assert_eq!(list.pop(), Some(&2 as &i32).copied());
        assert_eq!(list.len(), 2);
    }
}
