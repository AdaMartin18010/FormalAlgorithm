//! # 跳表 (Skip List)
//!
//! 跳表是一种概率性的数据结构，通过在多层链表上建立索引，实现类似平衡树的搜索效率。
//!
//! ## 复杂度分析
//! | 操作 | 平均时间 | 最坏时间 | 空间复杂度 |
//! |------|---------|---------|-----------|
//! | 查找 | O(log n) | O(n) | O(n) |
//! | 插入 | O(log n) | O(n) | O(n) |
//! | 删除 | O(log n) | O(n) | O(n) |

use rand::Rng;
use std::cmp::Ordering;

const MAX_LEVEL: usize = 32;
const P: f64 = 0.5;

/// 跳表节点
struct Node<T> {
    value: Option<T>,
    forward: Vec<*mut Node<T>>,
}

impl<T> Node<T> {
    fn new_head(level: usize) -> Self {
        Self {
            value: None,
            forward: vec![std::ptr::null_mut(); level],
        }
    }

    fn new(value: T, level: usize) -> Self {
        Self {
            value: Some(value),
            forward: vec![std::ptr::null_mut(); level],
        }
    }
}

/// 跳表结构
///
/// # 示例
/// ```
/// use formal_algorithms::skiplist::SkipList;
///
/// let mut list = SkipList::new();
/// list.insert(3);
/// list.insert(1);
/// list.insert(2);
///
/// assert!(list.contains(&2));
/// assert_eq!(list.len(), 3);
/// ```
pub struct SkipList<T: Ord> {
    head: Box<Node<T>>,
    level: usize,
    length: usize,
    max_level: usize,
    p: f64,
}

impl<T: Ord> SkipList<T> {
    pub fn new() -> Self {
        Self::with_params(MAX_LEVEL, P)
    }

    pub fn with_params(max_level: usize, p: f64) -> Self {
        Self {
            head: Box::new(Node::new_head(max_level)),
            level: 1,
            length: 0,
            max_level,
            p,
        }
    }

    fn random_level(&self) -> usize {
        let mut level = 1;
        let mut rng = rand::thread_rng();
        while level < self.max_level && rng.gen::<f64>() < self.p {
            level += 1;
        }
        level
    }

    unsafe fn get_next(node: *const Node<T>, level: usize) -> *mut Node<T> {
        (*node).forward.as_ptr().add(level).read()
    }

    unsafe fn set_next(node: *mut Node<T>, level: usize, next: *mut Node<T>) {
        (*node).forward.as_mut_ptr().add(level).write(next);
    }

    // value access is done inline to avoid lifetime issues with raw pointers

    pub fn contains(&self, target: &T) -> bool {
        unsafe {
            let mut current: *const Node<T> = &*self.head;
            for i in (0..self.level).rev() {
                loop {
                    let next = Self::get_next(current, i);
                    if next.is_null() {
                        break;
                    }
                    match (*next).value.as_ref().unwrap().cmp(target) {
                        Ordering::Less => current = next as *const _,
                        Ordering::Equal => return true,
                        Ordering::Greater => break,
                    }
                }
            }
            false
        }
    }

    pub fn insert(&mut self, value: T) {
        if self.contains(&value) {
            return;
        }

        let mut update: Vec<*mut Node<T>> = vec![&mut *self.head; self.max_level];
        let mut current: *mut Node<T> = &mut *self.head;

        unsafe {
            for i in (0..self.level).rev() {
                loop {
                    let next = Self::get_next(current, i);
                    if next.is_null() {
                        break;
                    }
                    if (*next).value.as_ref().unwrap() < &value {
                        current = next;
                    } else {
                        break;
                    }
                }
                update[i] = current;
            }
        }

        let new_level = self.random_level();
        if new_level > self.level {
            for i in self.level..new_level {
                update[i] = &mut *self.head;
            }
            self.level = new_level;
        }

        let new_node = Box::into_raw(Box::new(Node::new(value, new_level)));

        unsafe {
            for i in 0..new_level {
                let old_next = Self::get_next(update[i], i);
                Self::set_next(new_node, i, old_next);
                Self::set_next(update[i], i, new_node);
            }
        }

        self.length += 1;
    }

    pub fn remove(&mut self, target: &T) -> bool {
        let mut update: Vec<*mut Node<T>> = vec![&mut *self.head; self.max_level];
        let mut current: *mut Node<T> = &mut *self.head;
        let mut found = false;

        unsafe {
            for i in (0..self.level).rev() {
                loop {
                    let next = Self::get_next(current, i);
                    if next.is_null() {
                        break;
                    }
                    match (*next).value.as_ref().unwrap().cmp(target) {
                        Ordering::Less => current = next,
                        Ordering::Equal => {
                            found = true;
                            update[i] = current;
                            break;
                        }
                        Ordering::Greater => break,
                    }
                }
                if !found {
                    update[i] = current;
                }
            }
        }

        if !found {
            return false;
        }

        let mut to_free: *mut Node<T> = std::ptr::null_mut();
        unsafe {
            for i in 0..self.level {
                let next = Self::get_next(update[i], i);
                if !next.is_null() && (*next).value.as_ref().unwrap() == target {
                    let next_next = Self::get_next(next, i);
                    Self::set_next(update[i], i, next_next);
                    if to_free.is_null() {
                        to_free = next;
                    }
                }
            }
            if !to_free.is_null() {
                let _ = Box::from_raw(to_free);
            }
        }

        while self.level > 1 && unsafe { Self::get_next(&*self.head, self.level - 1).is_null() } {
            self.level -= 1;
        }

        self.length -= 1;
        true
    }

    pub fn range(&self, start: &T, end: &T) -> Vec<&T> {
        let mut result = Vec::new();
        unsafe {
            let mut current: *const Node<T> = &*self.head;
            for i in (0..self.level).rev() {
                loop {
                    let next = Self::get_next(current, i);
                    if next.is_null() {
                        break;
                    }
                    if (*next).value.as_ref().unwrap() < start {
                        current = next as *const _;
                    } else {
                        break;
                    }
                }
            }

            current = Self::get_next(current, 0);
            while !current.is_null() && (*current).value.as_ref().unwrap() <= end {
                result.push((*current).value.as_ref().unwrap());
                current = Self::get_next(current, 0);
            }
        }
        result
    }

    pub fn kth(&self, k: usize) -> Option<&T> {
        if k >= self.length {
            return None;
        }
        unsafe {
            let mut current = Self::get_next(&*self.head, 0);
            for _ in 0..k {
                if current.is_null() {
                    return None;
                }
                current = Self::get_next(current, 0);
            }
            if current.is_null() {
                None
            } else {
                Some((*current).value.as_ref().unwrap())
            }
        }
    }

    pub fn min(&self) -> Option<&T> {
        unsafe {
            let p = Self::get_next(&*self.head, 0);
            if p.is_null() {
                None
            } else {
                Some((*p).value.as_ref().unwrap())
            }
        }
    }

    pub fn max(&self) -> Option<&T> {
        unsafe {
            let mut current: *const Node<T> = &*self.head;
            for i in (0..self.level).rev() {
                loop {
                    let next = Self::get_next(current, i);
                    if next.is_null() {
                        break;
                    }
                    current = next as *const _;
                }
            }
            if current == &*self.head as *const _ {
                None
            } else {
                Some((*current).value.as_ref().unwrap())
            }
        }
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub fn clear(&mut self) {
        unsafe {
            let mut current = Self::get_next(&*self.head, 0);
            while !current.is_null() {
                let next = Self::get_next(current, 0);
                let _ = Box::from_raw(current);
                current = next;
            }
        }
        for i in 0..self.max_level {
            unsafe {
                Self::set_next(&mut *self.head, i, std::ptr::null_mut());
            }
        }
        self.level = 1;
        self.length = 0;
    }

    pub fn iter(&self) -> Vec<&T> {
        let mut result = Vec::new();
        unsafe {
            let mut current = Self::get_next(&*self.head, 0);
            while !current.is_null() {
                result.push((*current).value.as_ref().unwrap());
                current = Self::get_next(current, 0);
            }
        }
        result
    }

    pub fn level(&self) -> usize {
        self.level
    }
}

impl<T: Ord> Default for SkipList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord> Drop for SkipList<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut list = SkipList::new();
        list.insert(3);
        list.insert(1);
        list.insert(2);
        assert!(list.contains(&1));
        assert!(list.contains(&2));
        assert!(list.contains(&3));
        assert!(!list.contains(&4));
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn test_min_max() {
        let mut list = SkipList::new();
        assert_eq!(list.min(), None);
        list.insert(5);
        list.insert(1);
        list.insert(10);
        assert_eq!(list.min(), Some(&1));
        assert_eq!(list.max(), Some(&10));
    }

    #[test]
    fn test_remove() {
        let mut list = SkipList::new();
        list.insert(1);
        list.insert(3);
        list.insert(5);
        assert!(list.remove(&3));
        assert!(!list.contains(&3));
        assert!(list.contains(&1));
        assert!(list.contains(&5));
        assert_eq!(list.len(), 2);
    }

    #[test]
    fn test_range() {
        let mut list = SkipList::new();
        for v in [1, 3, 5, 7, 9] {
            list.insert(v);
        }
        let r = list.range(&3, &7);
        assert_eq!(r, vec![&3, &5, &7]);
    }

    #[test]
    fn test_kth() {
        let mut list = SkipList::new();
        for v in [10, 20, 30, 40] {
            list.insert(v);
        }
        assert_eq!(list.kth(0), Some(&10));
        assert_eq!(list.kth(3), Some(&40));
        assert_eq!(list.kth(4), None);
    }

    #[test]
    fn test_clear() {
        let mut list = SkipList::new();
        list.insert(1);
        list.insert(2);
        list.clear();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test_iter() {
        let mut list = SkipList::new();
        list.insert(3);
        list.insert(1);
        list.insert(2);
        assert_eq!(list.iter(), vec![&1, &2, &3]);
    }
}
