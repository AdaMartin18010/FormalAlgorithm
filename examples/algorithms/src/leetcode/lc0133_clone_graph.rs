//! LeetCode 133. Clone Graph
//! 链接: https://leetcode.com/problems/clone-graph/
//! 难度: Medium
//!
//! 算法: DFS/BFS + 哈希映射（引用不变式）
//! 时间复杂度: O(V + E)
//! 空间复杂度: O(V)

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Node {
    pub val: i32,
    pub neighbors: Vec<Rc<RefCell<Node>>>,
}

impl Node {
    pub fn new(val: i32) -> Rc<RefCell<Node>> {
        Rc::new(RefCell::new(Node {
            val,
            neighbors: Vec::new(),
        }))
    }
}

pub struct Solution;

impl Solution {
    /// 返回给定连通无向图的深拷贝。
    ///
    /// 形式化规约:
    /// - 前置条件: G = (V, E) 是连通无向图, |V| ∈ [1, 100]
    /// - 后置条件: 返回 G' ≅ G, 且 V' ∩ V = ∅（所有节点为新创建）
    ///
    /// 核心思路:
    ///   使用哈希表维护 "原节点 → 新节点" 的映射，防止环导致的无限递归。
    ///   DFS 遍历原图，每个原节点仅被复制一次。
    pub fn clone_graph(node: Option<Rc<RefCell<Node>>>) -> Option<Rc<RefCell<Node>>> {
        if node.is_none() {
            return None;
        }

        let mut visited: HashMap<i32, Rc<RefCell<Node>>> = HashMap::new();
        Self::dfs(node.unwrap(), &mut visited)
    }

    fn dfs(
        node: Rc<RefCell<Node>>,
        visited: &mut HashMap<i32, Rc<RefCell<Node>>>,
    ) -> Option<Rc<RefCell<Node>>> {
        let val = node.borrow().val;

        // 引用不变式: 若已复制，直接返回缓存的新节点
        if let Some(clone) = visited.get(&val) {
            return Some(clone.clone());
        }

        // 创建新节点并立即建立映射（打破环的循环依赖）
        let clone = Node::new(val);
        visited.insert(val, clone.clone());

        // 递归复制邻居
        for neighbor in &node.borrow().neighbors {
            if let Some(clone_neighbor) = Self::dfs(neighbor.clone(), visited) {
                clone.borrow_mut().neighbors.push(clone_neighbor);
            }
        }

        Some(clone)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_graph(adj_list: Vec<Vec<i32>>) -> Option<Rc<RefCell<Node>>> {
        if adj_list.is_empty() {
            return None;
        }

        let mut nodes: HashMap<i32, Rc<RefCell<Node>>> = HashMap::new();
        for i in 1..=adj_list.len() {
            nodes.insert(i as i32, Node::new(i as i32));
        }

        for (i, neighbors) in adj_list.iter().enumerate() {
            let val = (i + 1) as i32;
            for &n in neighbors {
                nodes
                    .get(&val)
                    .unwrap()
                    .borrow_mut()
                    .neighbors
                    .push(nodes.get(&n).unwrap().clone());
            }
        }

        Some(nodes.get(&1).unwrap().clone())
    }

    fn graph_to_adj_list(node: Option<Rc<RefCell<Node>>>) -> Vec<Vec<i32>> {
        if node.is_none() {
            return vec![];
        }

        let mut map: HashMap<i32, Vec<i32>> = HashMap::new();
        let mut stack = vec![node.unwrap()];
        let mut visited_vals = std::collections::HashSet::new();

        while let Some(n) = stack.pop() {
            let val = n.borrow().val;
            if visited_vals.contains(&val) {
                continue;
            }
            visited_vals.insert(val);

            let mut neighbors = Vec::new();
            for neighbor in &n.borrow().neighbors {
                neighbors.push(neighbor.borrow().val);
                stack.push(neighbor.clone());
            }
            neighbors.sort();
            map.insert(val, neighbors);
        }

        let max_val = *map.keys().max().unwrap();
        let mut result = Vec::new();
        for i in 1..=max_val {
            result.push(map.get(&i).cloned().unwrap_or_default());
        }
        result
    }

    #[test]
    fn test_clone_graph_basic() {
        let adj_list = vec![vec![2, 4], vec![1, 3], vec![2, 4], vec![1, 3]];
        let original = build_graph(adj_list.clone());
        let cloned = Solution::clone_graph(original);
        assert_eq!(graph_to_adj_list(cloned), adj_list);
    }

    #[test]
    fn test_clone_graph_single_node() {
        let adj_list = vec![vec![]];
        let original = build_graph(adj_list.clone());
        let cloned = Solution::clone_graph(original);
        assert_eq!(graph_to_adj_list(cloned), adj_list);
    }

    #[test]
    fn test_clone_graph_empty() {
        assert!(Solution::clone_graph(None).is_none());
    }
}
