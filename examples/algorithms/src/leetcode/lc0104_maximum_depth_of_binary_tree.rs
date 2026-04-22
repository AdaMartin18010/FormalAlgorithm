//! LeetCode 104. 二叉树的最大深度
//!
//! 给定一个二叉树 root，返回其最大深度。
//! 二叉树的最大深度是指从根节点到最远叶子节点的最长路径上的节点数。
//!
//! 对标: LeetCode 104 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

// Definition for a binary tree node.
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
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

/// 计算二叉树的最大深度。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：树中节点总数范围 `[0, 10^4]`。
/// - **后置条件 (Post)**：返回从根节点到最远叶子节点的路径上的节点数。
///
/// # 核心思路
///
/// 递归法（DFS）：树的最大深度 = 1 + max(左子树深度, 右子树深度)。空树深度为 0。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 访问每个节点一次。
/// - **空间复杂度**：O(h) — 递归栈深度，h 为树高；最坏情况 O(n)。
///
/// # 证明要点
///
/// - 归纳基础：空树深度为 0，叶子节点深度为 1，正确。
/// - 归纳步骤：假设左子树和右子树的 max_depth 分别正确返回 dl, dr。
///   则当前树的最大深度为 `1 + max(dl, dr)`，因为从根到最深叶子必须经过左或右子树最深路径。
pub fn max_depth(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    match root {
        None => 0,
        Some(node) => {
            let node = node.borrow();
            1 + max_depth(node.left.clone()).max(max_depth(node.right.clone()))
        }
    }
}

/// 迭代法（BFS 层序遍历）计算二叉树最大深度。
pub fn max_depth_bfs(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    let mut depth = 0;
    let mut queue: VecDeque<Option<Rc<RefCell<TreeNode>>>> = VecDeque::new();
    if root.is_some() {
        queue.push_back(root);
    }

    while !queue.is_empty() {
        depth += 1;
        let level_size = queue.len();
        for _ in 0..level_size {
            if let Some(Some(node)) = queue.pop_front() {
                let node = node.borrow();
                if node.left.is_some() {
                    queue.push_back(node.left.clone());
                }
                if node.right.is_some() {
                    queue.push_back(node.right.clone());
                }
            }
        }
    }

    depth
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 3,
            left: Some(Rc::new(RefCell::new(TreeNode::new(9)))),
            right: Some(Rc::new(RefCell::new(TreeNode {
                val: 20,
                left: Some(Rc::new(RefCell::new(TreeNode::new(15)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(7)))),
            }))),
        }));
        assert_eq!(max_depth(root.clone()), 3);
        assert_eq!(max_depth_bfs(root), 3);
    }

    #[test]
    fn test_example_2() {
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 1,
            left: None,
            right: Some(Rc::new(RefCell::new(TreeNode::new(2)))),
        })));
        assert_eq!(max_depth(root), 2);
    }

    #[test]
    fn test_empty() {
        assert_eq!(max_depth(None), 0);
    }

    #[test]
    fn test_single() {
        assert_eq!(max_depth(Some(Rc::new(RefCell::new(TreeNode::new(0))))), 1);
    }
}
