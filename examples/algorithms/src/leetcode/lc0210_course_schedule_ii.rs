//! LeetCode 210. Course Schedule II
//! 链接: https://leetcode.com/problems/course-schedule-ii/
//! 难度: Medium
//!
//! 算法: 拓扑排序（Kahn 算法 / BFS 入度法）
//! 时间复杂度: O(V + E)
//! 空间复杂度: O(V + E)

use std::collections::VecDeque;

pub struct Solution;

impl Solution {
    /// 返回一个合法的修课顺序（拓扑排序），若不可能则返回空数组。
    ///
    /// 形式化规约:
    /// - 前置条件: numCourses ∈ [1, 2000], prerequisites.length ∈ [0, 5000]
    /// - 后置条件: 返回拓扑排序数组，若图非 DAG 则返回 []
    ///
    /// 核心思路:
    ///   Kahn 算法的直接扩展：在环检测的同时输出拓扑序。
    ///   若输出顶点数等于 numCourses，则该顺序即为合法修课顺序。
    pub fn find_order(num_courses: i32, prerequisites: Vec<Vec<i32>>) -> Vec<i32> {
        let n = num_courses as usize;
        let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
        let mut in_degree: Vec<i32> = vec![0; n];

        for pre in prerequisites {
            let ai = pre[0] as usize;
            let bi = pre[1] as usize;
            adj[bi].push(ai);
            in_degree[ai] += 1;
        }

        let mut queue: VecDeque<usize> = VecDeque::new();
        for i in 0..n {
            if in_degree[i] == 0 {
                queue.push_back(i);
            }
        }

        let mut result: Vec<i32> = Vec::new();
        while let Some(node) = queue.pop_front() {
            result.push(node as i32);
            for &neighbor in &adj[node] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push_back(neighbor);
                }
            }
        }

        if result.len() == n {
            result
        } else {
            vec![]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let result = Solution::find_order(2, vec![vec![1, 0]]);
        assert_eq!(result, vec![0, 1]);
    }

    #[test]
    fn test_example_2() {
        let result = Solution::find_order(4, vec![vec![1, 0], vec![2, 0], vec![3, 1], vec![3, 2]]);
        // 合法拓扑序之一: [0, 1, 2, 3] 或 [0, 2, 1, 3]
        assert_eq!(result.len(), 4);
        assert!(is_valid_order(4, vec![vec![1, 0], vec![2, 0], vec![3, 1], vec![3, 2]], &result));
    }

    #[test]
    fn test_cycle() {
        let result = Solution::find_order(2, vec![vec![1, 0], vec![0, 1]]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_no_prerequisites() {
        let result = Solution::find_order(3, vec![]);
        assert_eq!(result.len(), 3);
    }

    fn is_valid_order(n: i32, prerequisites: Vec<Vec<i32>>, order: &[i32]) -> bool {
        if order.len() != n as usize {
            return false;
        }
        let mut pos = vec![0; n as usize];
        for (i, &v) in order.iter().enumerate() {
            pos[v as usize] = i;
        }
        for pre in prerequisites {
            if pos[pre[0] as usize] < pos[pre[1] as usize] {
                return false;
            }
        }
        true
    }
}
