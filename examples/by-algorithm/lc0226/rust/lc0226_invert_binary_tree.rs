/// LeetCode 226 - Invert Binary Tree
/// https://leetcode.com/problems/invert-binary-tree/
///
/// 题目：翻转一棵二叉树（镜像）。
///
/// 思路：递归后序遍历。先递归翻转左右子树，再交换当前节点的左右子节点指针。
/// 时间复杂度：O(n)
/// 空间复杂度：O(h)

use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

pub fn invert_tree(root: Option<Rc<RefCell<TreeNode>>>) -> Option<Rc<RefCell<TreeNode>>> {
    if let Some(node) = root {
        let mut n = node.borrow_mut();
        let left = n.left.take();
        let right = n.right.take();
        n.left = invert_tree(right);
        n.right = invert_tree(left);
        drop(n);
        Some(node)
    } else {
        None
    }
}

// 辅助函数：中序遍历用于验证
fn inorder(root: &Option<Rc<RefCell<TreeNode>>>, result: &mut Vec<i32>) {
    if let Some(n) = root {
        let n = n.borrow();
        inorder(&n.left, result);
        result.push(n.val);
        inorder(&n.right, result);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invert_normal() {
        // 原树：
        //      4
        //     / \
        //    2   7
        //   / \ / \
        //  1  3 6  9
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 4,
            left: Some(Rc::new(RefCell::new(TreeNode {
                val: 2,
                left: Some(Rc::new(RefCell::new(TreeNode::new(1)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(3)))),
            }))),
            right: Some(Rc::new(RefCell::new(TreeNode {
                val: 7,
                left: Some(Rc::new(RefCell::new(TreeNode::new(6)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(9)))),
            }))),
        })));

        let inverted = invert_tree(root);
        let mut result = Vec::new();
        inorder(&inverted, &mut result);
        // 翻转后中序应为：9, 7, 6, 4, 3, 2, 1
        assert_eq!(result, vec![9, 7, 6, 4, 3, 2, 1]);
    }

    #[test]
    fn test_invert_empty() {
        assert_eq!(invert_tree(None), None);
    }

    #[test]
    fn test_invert_single() {
        let root = Some(Rc::new(RefCell::new(TreeNode::new(1))));
        let inverted = invert_tree(root);
        let mut result = Vec::new();
        inorder(&inverted, &mut result);
        assert_eq!(result, vec![1]);
    }
}
