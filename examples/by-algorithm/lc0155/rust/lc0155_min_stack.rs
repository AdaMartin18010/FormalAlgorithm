//! LeetCode 155. Min Stack
//! 最小栈
//!
//! Design a stack that supports push, pop, top, and retrieving the minimum element in constant time.

pub struct MinStack {
    stack: Vec<i32>,
    min_stack: Vec<i32>,
}

impl MinStack {
    /// 初始化栈对象
    /// Initialize the stack object
    pub fn new() -> Self {
        MinStack {
            stack: Vec::new(),
            min_stack: Vec::new(),
        }
    }

    /// 将元素压入栈
    /// Push element onto stack
    pub fn push(&mut self, val: i32) {
        self.stack.push(val);
        let min_val = self.min_stack.last().map_or(val, |&m| m.min(val));
        self.min_stack.push(min_val);
    }

    /// 移除栈顶元素
    /// Remove the element on the top of the stack
    pub fn pop(&mut self) {
        self.stack.pop();
        self.min_stack.pop();
    }

    /// 获取栈顶元素
    /// Get the top element
    pub fn top(&self) -> i32 {
        *self.stack.last().unwrap()
    }

    /// 获取最小元素
    /// Retrieve the minimum element
    pub fn get_min(&self) -> i32 {
        *self.min_stack.last().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min_stack() {
        let mut ms = MinStack::new();
        ms.push(-2);
        ms.push(0);
        ms.push(-3);
        assert_eq!(ms.get_min(), -3);
        ms.pop();
        assert_eq!(ms.top(), 0);
        assert_eq!(ms.get_min(), -2);
    }
}
