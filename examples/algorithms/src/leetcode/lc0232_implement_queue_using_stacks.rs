//! LeetCode 232. Implement Queue using Stacks
//! 用栈实现队列
//!
//! Implement a first in first out (FIFO) queue using only two stacks.

pub struct MyQueue {
    in_stack: Vec<i32>,
    out_stack: Vec<i32>,
}

impl MyQueue {
    /// Initialize the queue object
    pub fn new() -> Self {
        MyQueue {
            in_stack: Vec::new(),
            out_stack: Vec::new(),
        }
    }

    /// Push element x to the back of queue
    pub fn push(&mut self, x: i32) {
        self.in_stack.push(x);
    }

    /// Removes the element from in front of queue and returns that element
    /// Amortized O(1)
    pub fn pop(&mut self) -> i32 {
        self.peek();
        self.out_stack.pop().unwrap()
    }

    /// Get the front element
    /// Transfer only when out_stack is empty
    pub fn peek(&mut self) -> i32 {
        if self.out_stack.is_empty() {
            while let Some(x) = self.in_stack.pop() {
                self.out_stack.push(x);
            }
        }
        *self.out_stack.last().unwrap()
    }

    /// Returns whether the queue is empty
    pub fn empty(&self) -> bool {
        self.in_stack.is_empty() && self.out_stack.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_queue_using_stacks() {
        let mut q = MyQueue::new();
        q.push(1);
        q.push(2);
        assert_eq!(q.peek(), 1);
        assert_eq!(q.pop(), 1);
        assert!(!q.empty());
        assert_eq!(q.pop(), 2);
        assert!(q.empty());
    }
}
