//! LeetCode 102. 二叉树的层序遍历
//!
//! 给定一个二叉树，返回其节点值的层序遍历（即逐层从左到右）。
//!
//! 对标: LeetCode 102 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

/// 二叉树节点定义。
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

/// 返回二叉树的层序遍历结果。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`root` 为二叉树根节点，或为 `None`。
/// - **后置条件 (Post)**：返回二维向量，第 i 个向量包含第 i 层所有节点值（从左到右）。
///
/// # BFS 层级不变式
///
/// 处理第 d 层前，队列中恰好包含第 d 层所有节点（从左到右顺序）。
/// 处理完成后，队列中恰好包含第 d+1 层所有节点。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — n 为节点总数，每个节点访问一次。
/// - **空间复杂度**：O(w) — w 为树的最大宽度，即队列最大长度。
///
/// # 证明要点
/// - 初始化：队列放入根节点，满足第 0 层不变式。
/// - 保持：处理当前层时，将每个节点的左右子节点依次入队，保证下一层节点顺序正确。
/// - 终止：队列为空时，所有层均已处理完毕。
pub fn level_order(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<Vec<i32>> {
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut queue = VecDeque::new();

    if let Some(node) = root {
        queue.push_back(node);
    }

    while !queue.is_empty() {
        let level_size = queue.len();
        let mut level = Vec::with_capacity(level_size);
        for _ in 0..level_size {
            let node = queue.pop_front().unwrap();
            let node_ref = node.borrow();
            level.push(node_ref.val);
            if let Some(left) = node_ref.left.clone() {
                queue.push_back(left);
            }
            if let Some(right) = node_ref.right.clone() {
                queue.push_back(right);
            }
        }
        result.push(level);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example() {
        let root = Some(Rc::new(RefCell::new(TreeNode {
            val: 3,
            left: Some(Rc::new(RefCell::new(TreeNode::new(9)))),
            right: Some(Rc::new(RefCell::new(TreeNode {
                val: 20,
                left: Some(Rc::new(RefCell::new(TreeNode::new(15)))),
                right: Some(Rc::new(RefCell::new(TreeNode::new(7)))),
            }))),
        })));
        assert_eq!(level_order(root), vec![vec![3], vec![9, 20], vec![15, 7]]);
    }

    #[test]
    fn test_empty_tree() {
        assert!(level_order(None).is_empty());
    }

    #[test]
    fn test_single_node() {
        let root = Some(Rc::new(RefCell::new(TreeNode::new(1))));
        assert_eq!(level_order(root), vec![vec![1]]);
    }
}
