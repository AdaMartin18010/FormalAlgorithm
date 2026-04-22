//! LeetCode 207. Course Schedule
//! 链接: https://leetcode.com/problems/course-schedule/
//! 难度: Medium
//!
//! 算法: 拓扑排序（Kahn 算法 / BFS 入度法）
//! 时间复杂度: O(V + E)
//! 空间复杂度: O(V + E)

use std::collections::VecDeque;

pub struct Solution;

impl Solution {
    /// 判断是否能完成所有课程（检测有向图是否存在环）。
    ///
    /// 形式化规约:
    /// - 前置条件: numCourses ∈ [1, 2000], prerequisites.length ∈ [0, 5000]
    /// - 后置条件: 返回 true 当且仅当课程依赖图是 DAG
    ///
    /// 核心思路:
    ///   Kahn 算法：计算每个节点的入度，将入度为 0 的节点加入队列。
    ///   依次取出节点，将其邻接节点入度减 1；若邻接节点入度变为 0，入队。
    ///   若处理的节点数等于总节点数，则图无环（存在拓扑排序）。
    pub fn can_finish(num_courses: i32, prerequisites: Vec<Vec<i32>>) -> bool {
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

        let mut processed = 0;
        while let Some(node) = queue.pop_front() {
            processed += 1;
            for &neighbor in &adj[node] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push_back(neighbor);
                }
            }
        }

        processed == n
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(Solution::can_finish(2, vec![vec![1, 0]]));
    }

    #[test]
    fn test_example_2() {
        assert!(!Solution::can_finish(2, vec![vec![1, 0], vec![0, 1]]));
    }

    #[test]
    fn test_no_prerequisites() {
        assert!(Solution::can_finish(3, vec![]));
    }

    #[test]
    fn test_cycle_of_three() {
        assert!(!Solution::can_finish(3, vec![vec![1, 0], vec![2, 1], vec![0, 2]]));
    }

    #[test]
    fn test_dag() {
        assert!(Solution::can_finish(
            4,
            vec![vec![1, 0], vec![2, 0], vec![3, 1], vec![3, 2]]
        ));
    }
}
