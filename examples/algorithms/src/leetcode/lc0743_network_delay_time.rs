//! LeetCode 743. Network Delay Time
//! 链接: https://leetcode.com/problems/network-delay-time/
//! 难度: Medium
//!
//! 算法: Dijkstra（单源最短路径）
//! 时间复杂度: O((V + E) log V)
//! 空间复杂度: O(V + E)

use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};

pub struct Solution;

impl Solution {
    /// 返回信号从节点 k 出发，覆盖全网所需的最短时间。
    ///
    /// 形式化规约:
    /// - 前置条件: G = (V, E), |V| = n ∈ [1, 100], w(u,v) > 0
    /// - 后置条件: 返回 max_{v∈V} δ(k, v)，若存在不可达节点则返回 -1
    ///
    /// 核心思路:
    ///   Dijkstra 贪心算法。维护已确定最短距离的集合 S，每次从优先队列中
    ///   取出当前距离估计最小的顶点 u，将其加入 S，并松弛其所有出边。
    pub fn network_delay_time(times: Vec<Vec<i32>>, n: i32, k: i32) -> i32 {
        let n = n as usize;
        let k = (k - 1) as usize; // 转为 0-based

        // 建图（邻接表）
        let mut graph: Vec<Vec<(usize, i32)>> = vec![vec![]; n];
        for edge in times {
            let u = (edge[0] - 1) as usize;
            let v = (edge[1] - 1) as usize;
            let w = edge[2];
            graph[u].push((v, w));
        }

        // Dijkstra
        const INF: i32 = i32::MAX;
        let mut dist: Vec<i32> = vec![INF; n];
        let mut visited = vec![false; n];
        let mut heap: BinaryHeap<Reverse<(i32, usize)>> = BinaryHeap::new();

        dist[k] = 0;
        heap.push(Reverse((0, k)));

        while let Some(Reverse((d, u))) = heap.pop() {
            if visited[u] {
                continue;
            }
            visited[u] = true;

            for &(v, w) in &graph[u] {
                if !visited[v] && dist[u] + w < dist[v] {
                    dist[v] = dist[u] + w;
                    heap.push(Reverse((dist[v], v)));
                }
            }
        }

        let max_dist = *dist.iter().max().unwrap();
        if max_dist == INF {
            -1
        } else {
            max_dist
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let times = vec![vec![2, 1, 1], vec![2, 3, 1], vec![3, 4, 1]];
        assert_eq!(Solution::network_delay_time(times, 4, 2), 2);
    }

    #[test]
    fn test_example_2() {
        let times = vec![vec![1, 2, 1]];
        assert_eq!(Solution::network_delay_time(times, 2, 1), 1);
    }

    #[test]
    fn test_unreachable() {
        let times = vec![vec![1, 2, 1]];
        assert_eq!(Solution::network_delay_time(times, 2, 2), -1);
    }

    #[test]
    fn test_single_node() {
        assert_eq!(Solution::network_delay_time(vec![], 1, 1), 0);
    }
}
