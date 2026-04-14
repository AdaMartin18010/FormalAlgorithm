//! Floyd-Warshall 全对最短路径算法
//!
//! 使用动态规划求解所有顶点对之间的最短路径。
//! 支持负权边，可检测负权环。
//! 对标: CLRS Chapter 25.2

use crate::AlgorithmError;

/// Floyd-Warshall 算法结果
#[derive(Debug, Clone, PartialEq)]
pub struct FloydWarshallResult<W> {
    /// 距离矩阵，result.dist[i][j] 为 i 到 j 的最短距离
    pub dist: Vec<Vec<W>>,
    /// 后继矩阵，用于重建路径
    pub next: Vec<Vec<Option<usize>>>,
}

impl<W: Clone> FloydWarshallResult<W> {
    /// 重建从 u 到 v 的最短路径
    ///
    /// # 返回值
    ///
    /// 若 u == v，返回 `Some(vec![u])`；
    /// 若不可达，返回 `None`。
    pub fn path(&self, u: usize, v: usize) -> Option<Vec<usize>> {
        if u == v {
            return Some(vec![u]);
        }
        if self.next[u][v].is_none() {
            return None;
        }
        let mut path = vec![u];
        let mut at = u;
        while at != v {
            at = self.next[at][v]?;
            path.push(at);
        }
        Some(path)
    }
}

/// Floyd-Warshall 全对最短路径算法
///
/// # 算法说明
///
/// 状态转移：$d^{(k)}_{ij} = \min(d^{(k-1)}_{ij}, d^{(k-1)}_{ik} + d^{(k-1)}_{kj})$
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V³)
/// - **空间复杂度**：O(V²)
///
/// # 参数
///
/// * `n` - 顶点数量（顶点编号为 0 到 n-1）
/// * `edges` - 边列表，每条边为 (u, v, weight)
///
/// # 返回值
///
/// 成功时返回 `FloydWarshallResult`，失败时返回 `AlgorithmError::GraphError`（存在负权环）
///
/// # 示例
///
/// ```
/// use formal_algorithms::floyd_warshall::floyd_warshall;
///
/// let edges = vec![
///     (0, 1, 3),
///     (0, 3, 7),
///     (1, 0, 8),
///     (1, 2, 2),
///     (2, 0, 5),
///     (2, 3, 1),
///     (3, 0, 2),
/// ];
///
/// let result = floyd_warshall(4, &edges).unwrap();
/// assert_eq!(result.dist[0][2], 5); // 0->1->2 = 3+2 = 5
/// assert_eq!(result.dist[1][3], 3); // 1->2->3 = 2+1 = 3
/// ```
pub fn floyd_warshall<W>(
    n: usize,
    edges: &[(usize, usize, W)],
) -> Result<FloydWarshallResult<W>, AlgorithmError>
where
    W: Clone + Ord + std::ops::Add<Output = W> + Default + From<i32>,
{
    let inf = W::from(i32::MAX);
    let mut dist = vec![vec![inf.clone(); n]; n];
    let mut next = vec![vec![None; n]; n];

    for i in 0..n {
        dist[i][i] = W::default();
    }

    for &(u, v, ref w) in edges.iter() {
        if u >= n || v >= n {
            return Err(AlgorithmError::InvalidInput(
                "Vertex index out of bounds".to_string(),
            ));
        }
        if w.clone() < dist[u][v] {
            dist[u][v] = w.clone();
            next[u][v] = Some(v);
        }
    }

    for k in 0..n {
        for i in 0..n {
            if dist[i][k] == inf {
                continue;
            }
            for j in 0..n {
                if dist[k][j] == inf {
                    continue;
                }
                let via = dist[i][k].clone() + dist[k][j].clone();
                if via < dist[i][j] {
                    dist[i][j] = via;
                    next[i][j] = next[i][k];
                }
            }
        }
    }

    // 检测负权环
    for i in 0..n {
        if dist[i][i] < W::default() {
            return Err(AlgorithmError::GraphError(
                "Negative-weight cycle detected".to_string(),
            ));
        }
    }

    Ok(FloydWarshallResult { dist, next })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let edges = vec![
            (0, 1, 3),
            (0, 3, 7),
            (1, 0, 8),
            (1, 2, 2),
            (2, 0, 5),
            (2, 3, 1),
            (3, 0, 2),
        ];
        let result = floyd_warshall(4, &edges).unwrap();
        assert_eq!(result.dist[0][0], 0);
        assert_eq!(result.dist[0][2], 5);
        assert_eq!(result.dist[1][3], 3);
        assert_eq!(result.dist[3][2], 7); // 3->0->1->2 = 2+3+2 = 7
    }

    #[test]
    fn test_negative_cycle() {
        let edges = vec![(0, 1, 1), (1, 2, -3), (2, 0, 1)];
        let result = floyd_warshall(3, &edges);
        assert!(matches!(result, Err(AlgorithmError::GraphError(_))));
    }

    #[test]
    fn test_disconnected() {
        let edges = vec![(0, 1, 5)];
        let result = floyd_warshall(3, &edges).unwrap();
        assert_eq!(result.dist[0][1], 5);
        assert_eq!(result.dist[0][2], i32::MAX);
        assert!(result.path(0, 2).is_none());
    }

    #[test]
    fn test_path_reconstruction() {
        let edges = vec![(0, 1, 3), (1, 2, 2), (2, 3, 1)];
        let result = floyd_warshall(4, &edges).unwrap();
        let path = result.path(0, 3).unwrap();
        assert_eq!(path, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_same_vertex_path() {
        let result: FloydWarshallResult<i32> = floyd_warshall(2, &[]).unwrap();
        assert_eq!(result.path(0, 0), Some(vec![0]));
    }
}
