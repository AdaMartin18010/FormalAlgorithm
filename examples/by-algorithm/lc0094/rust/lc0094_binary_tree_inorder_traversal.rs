/// LeetCode 94 - Binary Tree Inorder Traversal
/// https://leetcode.com/problems/binary-tree-inorder-traversal/
///
/// 题目：给定二叉树根节点，返回其节点值的中序遍历（左-根-右）。
///
/// 思路：递归 DFS。先递归遍历左子树，再访问根节点，最后递归遍历右子树。
/// 时间复杂度：O(n)
/// 空间复杂度：O(h)，h 为树高（递归栈）

use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone)]
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

pub fn inorder_traversal(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<i32> {
    let mut result = Vec::new();
    fn dfs(node: &Option<Rc<RefCell<TreeNode>>>, result: &mut Vec<i32>) {
        if let Some(n) = node {
            let n = n.borrow();
            dfs(&n.left, result);
            result.push(n.val);
            dfs(&n.right, result);
        }
    }
    dfs(&root, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inorder_normal() {
        // 树结构：
        //      1
        //       \
        //        2
        //       /
        //      3
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 1,
            left: None,
            right: Some(Rc::new(RefCell::new(TreeNode {
                val: 2,
                left: Some(Rc::new(RefCell::new(TreeNode::new(3)))),
                right: None,
            }))),
        })));
        assert_eq!(inorder_traversal(root), vec![1, 3, 2]);
    }

    #[test]
    fn test_inorder_empty() {
        assert_eq!(inorder_traversal(None), Vec::<i32>::new());
    }

    #[test]
    fn test_inorder_single() {
        let root = Some(Rc::new(RefCell::new(TreeNode::new(42))));
        assert_eq!(inorder_traversal(root), vec![42]);
    }

    #[test]
    fn test_inorder_complete() {
        //      4
        //     / \
        //    2   6
        //   / \ / \
        //  1  3 5  7
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 4,
            left: Some(Rc::new(RefCell::new(TreeNode {
                val: 2,
                left: Some(Rc::new(RefCell::new(TreeNode::new(1)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(3)))),
            }))),
            right: Some(Rc::new(RefCell::new(TreeNode {
                val: 6,
                left: Some(Rc::new(RefCell::new(TreeNode::new(5)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(7)))),
            }))),
        })));
        assert_eq!(inorder_traversal(root), vec![1, 2, 3, 4, 5, 6, 7]);
    }
}
