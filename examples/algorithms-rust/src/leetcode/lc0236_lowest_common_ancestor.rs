//! LeetCode 236. Lowest Common Ancestor of a Binary Tree
//! 链接: https://leetcode.com/problems/lowest-common-ancestor-of-a-binary-tree/
//! 难度: Medium
//!
//! 题目描述:
//! 给定一个二叉树, 找到该树中两个指定节点的最近公共祖先。
//!
//! 形式化规约:
//!   输入: 二叉树根节点 root，两个目标节点 p, q
//!   输出: p 和 q 的最近公共祖先
//!
//! 最优解思路:
//!   递归后序遍历：在左右子树中分别查找 p 和 q。
//!   - 若当前节点为 p 或 q，返回当前节点
//!   - 若左子树找到且右子树也找到，当前节点为 LCA
//!   - 若只有一侧找到，将该结果向上传递
//!
//! 复杂度:
//!   时间: O(n)
//!   空间: O(h)，h 为树高
//!
//! 正确性要点:
//!   1. 该解法假设 p 和 q 一定存在于树中
//!   2. 核心逻辑: if left and right { return root } else { return left or right }
//!   3. 若节点值唯一，也可用哈希表存储父指针后求交点

use std::cell::RefCell;
use std::rc::Rc;

pub type TreeNodeRef = Option<Rc<RefCell<TreeNode>>>;

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: TreeNodeRef,
    pub right: TreeNodeRef,
}

impl TreeNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

pub struct Solution;

impl Solution {
    pub fn lowest_common_ancestor(
        root: TreeNodeRef,
        p: TreeNodeRef,
        q: TreeNodeRef,
    ) -> TreeNodeRef {
        Self::helper(root, p, q)
    }

    fn helper(node: TreeNodeRef, p: TreeNodeRef, q: TreeNodeRef) -> TreeNodeRef {
        if node.is_none() {
            return None;
        }

        // 若当前节点为 p 或 q，直接返回
        if Rc::ptr_eq(
            node.as_ref().unwrap(),
            p.as_ref().unwrap(),
        ) || Rc::ptr_eq(
            node.as_ref().unwrap(),
            q.as_ref().unwrap(),
        ) {
            return node;
        }

        let left = Self::helper(
            node.as_ref().unwrap().borrow().left.clone(),
            p.clone(),
            q.clone(),
        );
        let right = Self::helper(
            node.as_ref().unwrap().borrow().right.clone(),
            p.clone(),
            q.clone(),
        );

        // 左右均找到，当前为 LCA
        if left.is_some() && right.is_some() {
            return node;
        }

        // 只有一侧找到，返回该侧结果
        if left.is_some() {
            left
        } else {
            right
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_tree(vals: &[Option<i32>], idx: usize) -> TreeNodeRef {
        if idx >= vals.len() || vals[idx].is_none() {
            return None;
        }
        let mut node = TreeNode::new(vals[idx].unwrap());
        node.left = build_tree(vals, 2 * idx + 1);
        node.right = build_tree(vals, 2 * idx + 2);
        Some(Rc::new(RefCell::new(node)))
    }

    // 简单测试: 构建一个小树并验证 LCA
    #[test]
    fn test_lca_simple() {
        //       3
        //      / \
        //     5   1
        //    / \ / \
        //   6  2 0  8
        //     / \
        //    7   4
        let root = build_tree(
            &[
                Some(3), Some(5), Some(1),
                Some(6), Some(2), Some(0), Some(8),
                None, None, Some(7), Some(4),
            ],
            0,
        );
        assert!(root.is_some());
        // 测试 p=5, q=1 -> LCA=3
        let p = root.as_ref().unwrap().borrow().left.clone(); // 5
        let q = root.as_ref().unwrap().borrow().right.clone(); // 1
        let lca = Solution::lowest_common_ancestor(root.clone(), p, q);
        assert_eq!(lca.as_ref().unwrap().borrow().val, 3);
    }
}
