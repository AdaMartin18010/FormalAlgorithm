//! LeetCode 1584. Min Cost to Connect All Points
//! 链接: https://leetcode.com/problems/min-cost-to-connect-all-points/
//! 难度: Medium
//!
//! 算法: Prim（稠密图数组实现，O(V²)）
//! 时间复杂度: O(n²)
//! 空间复杂度: O(n)

pub struct Solution;

impl Solution {
    /// 返回连接所有点的最小费用（曼哈顿距离 MST）。
    ///
    /// 形式化规约:
    /// - 前置条件: points ∈ ℤ^(n×2), n ∈ [1, 1000]
    /// - 后置条件: 返回 MST 的总权重，边权为曼哈顿距离
    ///
    /// 核心思路:
    ///   Prim 算法（数组版）。维护每个顶点到当前树的最小距离 min_dist，
    ///   每次选择距离最小的顶点加入树，并更新其他顶点到树的最小距离。
    ///   稠密图下数组版 Prim O(V²) 优于堆版 O(E log V) = O(V² log V)。
    pub fn min_cost_connect_points(points: Vec<Vec<i32>>) -> i32 {
        let n = points.len();
        if n <= 1 {
            return 0;
        }

        let mut min_dist: Vec<i32> = vec![i32::MAX; n]; // 每个点到树的最小距离
        let mut in_mst = vec![false; n];
        let mut total_cost = 0;

        min_dist[0] = 0;

        for _ in 0..n {
            // 找到当前距离树最近的顶点
            let mut u = 0;
            let mut min_d = i32::MAX;
            for i in 0..n {
                if !in_mst[i] && min_dist[i] < min_d {
                    min_d = min_dist[i];
                    u = i;
                }
            }

            in_mst[u] = true;
            total_cost += min_d;

            // 更新其他顶点到树的最小距离
            for v in 0..n {
                if !in_mst[v] {
                    let dist = Self::manhattan(&points[u], &points[v]);
                    if dist < min_dist[v] {
                        min_dist[v] = dist;
                    }
                }
            }
        }

        total_cost
    }

    fn manhattan(a: &[i32], b: &[i32]) -> i32 {
        (a[0] - b[0]).abs() + (a[1] - b[1]).abs()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let points = vec![vec![0, 0], vec![2, 2], vec![3, 10], vec![5, 2], vec![7, 0]];
        assert_eq!(Solution::min_cost_connect_points(points), 20);
    }

    #[test]
    fn test_example_2() {
        let points = vec![vec![3, 12], vec![-2, 5], vec![-4, 1]];
        assert_eq!(Solution::min_cost_connect_points(points), 18);
    }

    #[test]
    fn test_single_point() {
        assert_eq!(Solution::min_cost_connect_points(vec![vec![0, 0]]), 0);
    }

    #[test]
    fn test_two_points() {
        let points = vec![vec![0, 0], vec![1, 1]];
        assert_eq!(Solution::min_cost_connect_points(points), 2);
    }
}
