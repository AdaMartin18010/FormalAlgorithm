//! LeetCode 787. Cheapest Flights Within K Stops
//! 链接: https://leetcode.com/problems/cheapest-flights-within-k-stops/
//! 难度: Medium
//!
//! 算法: Bellman-Ford（K+1 轮松弛）
//! 时间复杂度: O(K * E)
//! 空间复杂度: O(V)

pub struct Solution;

impl Solution {
    /// 返回从 src 到 dst 最多经过 K 次中转的最便宜票价。
    ///
    /// 形式化规约:
    /// - 前置条件: n ∈ [1, 100], flights.length ∈ [0, n(n-1)], K ∈ [0, n]
    /// - 后置条件: 返回最多使用 K+1 条边的最短路径权重，若不存在则返回 -1
    ///
    /// 核心思路:
    ///   Bellman-Ford 的动态规划视角：dist_k[v] 表示最多使用 k 条边到达 v 的最小代价。
    ///   进行 K+1 轮松弛（每轮遍历所有边），使用辅助数组防止同轮内的串联更新。
    pub fn find_cheapest_price(
        n: i32,
        flights: Vec<Vec<i32>>,
        src: i32,
        dst: i32,
        k: i32,
    ) -> i32 {
        let n = n as usize;
        let src = src as usize;
        let dst = dst as usize;
        let k = k as usize;

        const INF: i32 = i32::MAX / 2;
        let mut dist: Vec<i32> = vec![INF; n];
        dist[src] = 0;

        // K+1 轮松弛（中转 K 次 = 最多 K+1 条边）
        for _ in 0..=k {
            let mut new_dist = dist.clone();
            for edge in &flights {
                let u = edge[0] as usize;
                let v = edge[1] as usize;
                let w = edge[2];
                if dist[u] + w < new_dist[v] {
                    new_dist[v] = dist[u] + w;
                }
            }
            dist = new_dist;
        }

        if dist[dst] == INF {
            -1
        } else {
            dist[dst]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let flights = vec![
            vec![0, 1, 100],
            vec![1, 2, 100],
            vec![2, 0, 100],
            vec![1, 3, 600],
            vec![2, 3, 200],
        ];
        assert_eq!(Solution::find_cheapest_price(4, flights, 0, 3, 1), 700);
    }

    #[test]
    fn test_example_2() {
        let flights = vec![
            vec![0, 1, 100],
            vec![1, 2, 100],
            vec![0, 2, 500],
        ];
        assert_eq!(Solution::find_cheapest_price(3, flights, 0, 2, 1), 200);
    }

    #[test]
    fn test_no_route() {
        let flights = vec![vec![0, 1, 100]];
        assert_eq!(Solution::find_cheapest_price(2, flights, 1, 0, 0), -1);
    }

    #[test]
    fn test_direct_flight() {
        let flights = vec![vec![0, 1, 100], vec![0, 1, 50]];
        assert_eq!(Solution::find_cheapest_price(2, flights, 0, 1, 0), 50);
    }
}
