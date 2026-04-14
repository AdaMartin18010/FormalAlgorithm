//! # 栈 (Stack)
//!
//! 后进先出 (LIFO) 的线性数据结构。
//!
//! ## 核心思想
//! - 仅允许在栈顶（top）进行插入（push）与删除（pop）操作
//! - 典型应用：表达式求值、括号匹配、函数调用栈、深度优先搜索（DFS）
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | push | O(1) 均摊 | O(1) |
//! | pop | O(1) 均摊 | O(1) |
//! | peek | O(1) | O(1) |

/// 栈结构
///
/// # 示例
/// ```
/// use formal_algorithms::stack::Stack;
///
/// let mut stack = Stack::new();
/// stack.push(1);
/// stack.push(2);
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.peek(), Some(&1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stack<T> {
    data: Vec<T>,
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Stack<T> {
    /// 创建空栈
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// 创建指定初始容量的栈
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    /// 将元素压入栈顶
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }

    /// 弹出栈顶元素
    pub fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }

    /// 查看栈顶元素（不弹出）
    pub fn peek(&self) -> Option<&T> {
        self.data.last()
    }

    /// 查看栈顶元素的可变引用
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.data.last_mut()
    }

    /// 返回栈中元素个数
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// 检查栈是否为空
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// 清空栈
    pub fn clear(&mut self) {
        self.data.clear();
    }
}

/// 括号匹配检查
///
/// # 示例
/// ```
/// use formal_algorithms::stack::is_balanced;
///
/// assert!(is_balanced("({[]})"));
/// assert!(!is_balanced("({[})"));
/// ```
pub fn is_balanced(s: &str) -> bool {
    let mut stack = Vec::new();
    for ch in s.chars() {
        match ch {
            '(' | '[' | '{' => stack.push(ch),
            ')' => {
                if stack.pop() != Some('(') {
                    return false;
                }
            }
            ']' => {
                if stack.pop() != Some('[') {
                    return false;
                }
            }
            '}' => {
                if stack.pop() != Some('{') {
                    return false;
                }
            }
            _ => {}
        }
    }
    stack.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_operations() {
        let mut stack = Stack::new();
        assert!(stack.is_empty());
        stack.push(10);
        stack.push(20);
        stack.push(30);
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.peek(), Some(&30));
        assert_eq!(stack.pop(), Some(30));
        assert_eq!(stack.pop(), Some(20));
        assert_eq!(stack.peek_mut(), Some(&mut 10));
        stack.clear();
        assert!(stack.is_empty());
    }

    #[test]
    fn test_is_balanced() {
        assert!(is_balanced("()"));
        assert!(is_balanced("({[]})"));
        assert!(is_balanced(""));
        assert!(!is_balanced("("));
        assert!(!is_balanced("]"));
        assert!(!is_balanced("({[})"));
    }
}
