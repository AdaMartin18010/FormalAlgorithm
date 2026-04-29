//! LeetCode 20. Valid Parentheses
//! 有效的括号
//!
//! Given a string s containing just the characters '(', ')', '{', '}', '[' and ']',
//! determine if the input string is valid.

/// 使用栈进行括号匹配
/// Stack-based parenthesis matching
/// Time: O(n), Space: O(n)
pub fn is_valid(s: String) -> bool {
    let mut stack: Vec<char> = Vec::new();

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
    fn test_valid_parentheses() {
        assert!(is_valid("()".to_string()));
        assert!(is_valid("()[]{}".to_string()));
        assert!(!is_valid("(]".to_string()));
        assert!(!is_valid("([)]".to_string()));
        assert!(is_valid("{[]}".to_string()));
    }
}
