//! Hopcroft-Karp 二分图最大匹配算法
//!
//! 时间复杂度: O(E * sqrt(V))
//! 对标: CLRS Chapter 26 问题 26-6

use std::collections::VecDeque;

/// Hopcroft-Karp 匹配结果
#[derive(Debug, Clone, PartialEq)]
pub struct HopcroftKarpResult {
    /// 左部顶点数量
    pub n_left: usize,
    /// 右部顶点数量
    pub n_right: usize,
    /// 左部顶点 u 的匹配对象，未匹配时为 None
    pub pair_left: Vec<Option<usize>>,
    /// 右部顶点 v 的匹配对象，未匹配时为 None
    pub pair_right: Vec<Option<usize>>,
    /// 匹配数
    pub matching_size: usize,
}

impl HopcroftKarpResult {
    /// 获取匹配边列表
    pub fn edges(&self) -> Vec<(usize, usize)> {
        self.pair_left
            .iter()
            .enumerate()
            .filter_map(|(u, v)| v.map(|v| (u, v)))
            .collect()
    }

    /// 检查是否为完美匹配
    pub fn is_perfect_matching(&self) -> bool {
        self.matching_size == self.n_left && self.matching_size == self.n_right
    }
}

fn dfs_hopcroft_karp(
    u: usize,
    adj: &[Vec<usize>],
    pair_left: &mut Vec<Option<usize>>,
    pair_right: &mut Vec<Option<usize>>,
    dist: &mut [usize],
) -> bool {
    for i in 0..adj[u].len() {
        let v = adj[u][i];
        if let Some(u2) = pair_right[v] {
            if dist[u2] == dist[u] + 1 && dfs_hopcroft_karp(u2, adj, pair_left, pair_right, dist) {
                pair_left[u] = Some(v);
                pair_right[v] = Some(u);
                return true;
            }
        } else {
            pair_left[u] = Some(v);
            pair_right[v] = Some(u);
            return true;
        }
    }
    dist[u] = usize::MAX;
    false
}

/// Hopcroft-Karp 二分图最大匹配算法
///
/// # 算法说明
///
/// 1. 初始化匹配为空。
/// 2. 使用 BFS 构建分层图，找到最短增广路的长度。
/// 3. 使用 DFS 在该分层图中寻找极大点不交最短增广路集合，并进行增广。
/// 4. 重复步骤 2-3 直到不存在增广路。
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(E * sqrt(V))
/// - **空间复杂度**: O(V + E)
///
/// # 参数
///
/// * `n_left` - 左部顶点数（编号 0..n_left-1）
/// * `n_right` - 右部顶点数（编号 0..n_right-1）
/// * `edges` - 边列表，每条边为 (u, v) 表示左部 u 与右部 v 相连
///
/// # 返回值
///
/// 返回 `HopcroftKarpResult`，包含最大匹配信息
///
/// # 示例
///
/// ```
/// use formal_algorithms::hopcroft_karp::hopcroft_karp;
///
/// let edges = vec![
///     (0, 0), (0, 1),
///     (1, 1), (1, 2),
///     (2, 2), (2, 3),
///     (3, 3),
/// ];
///
/// let result = hopcroft_karp(4, 4, &edges);
/// assert_eq!(result.matching_size, 4);
/// assert!(result.is_perfect_matching());
/// ```
pub fn hopcroft_karp(n_left: usize, n_right: usize, edges: &[(usize, usize)]) -> HopcroftKarpResult {
    let mut adj = vec![Vec::new(); n_left];
    for (u, v) in edges.iter() {
        if *u < n_left && *v < n_right {
            adj[*u].push(*v);
        }
    }

    let mut pair_left = vec![None; n_left];
    let mut pair_right = vec![None; n_right];
    let mut dist = vec![0; n_left];

    let mut matching_size = 0;

    loop {
        // BFS 构建分层图
        let mut queue = VecDeque::new();
        for u in 0..n_left {
            if pair_left[u].is_none() {
                dist[u] = 0;
                queue.push_back(u);
            } else {
                dist[u] = usize::MAX;
            }
        }

        let mut found_free_right = false;

        while let Some(u) = queue.pop_front() {
            for &v in &adj[u] {
                if let Some(u2) = pair_right[v] {
                    if dist[u2] == usize::MAX {
                        dist[u2] = dist[u] + 1;
                        queue.push_back(u2);
                    }
                } else {
                    found_free_right = true; // 找到可到达的未匹配右部顶点
                }
            }
        }

        if !found_free_right {
            break;
        }

        // DFS 寻找增广路
        for u in 0..n_left {
            if pair_left[u].is_none() && dfs_hopcroft_karp(u, &adj, &mut pair_left, &mut pair_right, &mut dist) {
                matching_size += 1;
            }
        }
    }

    HopcroftKarpResult {
        n_left,
        n_right,
        pair_left,
        pair_right,
        matching_size,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_perfect_matching() {
        let edges = vec![
            (0, 0),
            (0, 1),
            (1, 1),
            (1, 2),
            (2, 2),
            (2, 3),
            (3, 3),
        ];
        let result = hopcroft_karp(4, 4, &edges);
        assert_eq!(result.matching_size, 4);
        assert!(result.is_perfect_matching());
    }

    #[test]
    fn test_maximum_matching() {
        let edges = vec![
            (0, 0),
            (0, 1),
            (1, 0),
            (1, 1),
            (2, 0),
            (2, 1),
        ];
        let result = hopcroft_karp(3, 2, &edges);
        assert_eq!(result.matching_size, 2);
        assert!(!result.is_perfect_matching());
    }

    #[test]
    fn test_empty_graph() {
        let result = hopcroft_karp(3, 3, &[]);
        assert_eq!(result.matching_size, 0);
        assert!(result.edges().is_empty());
    }

    #[test]
    fn test_single_edge() {
        let result = hopcroft_karp(2, 2, &[(0, 1)]);
        assert_eq!(result.matching_size, 1);
        assert_eq!(result.edges(), vec![(0, 1)]);
    }

    #[test]
    fn test_disconnected() {
        let edges = vec![(0, 0), (2, 1)];
        let result = hopcroft_karp(3, 2, &edges);
        assert_eq!(result.matching_size, 2);
    }
}
