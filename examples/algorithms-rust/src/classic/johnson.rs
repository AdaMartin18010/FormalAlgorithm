//! Johnson 全对最短路径算法
//!
//! 适用于稀疏图，通过重赋权将负权边转化为非负权边，
//! 然后对每个顶点运行 Dijkstra 算法。
//! 支持负权边，可检测负权环。
//! 对标: CLRS Chapter 25.3

use std::cmp::Ordering;
use std::collections::BinaryHeap;

use super::bellman_ford::bellman_ford;
use crate::AlgorithmError;

/// Johnson 算法结果
#[derive(Debug, Clone, PartialEq)]
pub struct JohnsonResult<W> {
    /// 距离矩阵，result.dist[i][j] 为 i 到 j 的最短距离
    pub dist: Vec<Vec<W>>,
    /// 后继矩阵，用于重建路径
    pub next: Vec<Vec<Option<usize>>>,
}

impl<W: Clone> JohnsonResult<W> {
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

#[derive(Debug, Clone)]
struct State<W> {
    distance: W,
    vertex: usize,
}

impl<W: PartialEq> PartialEq for State<W> {
    fn eq(&self, other: &Self) -> bool {
        self.distance == other.distance
    }
}

impl<W: Eq> Eq for State<W> {}

impl<W: PartialOrd> PartialOrd for State<W> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        other.distance.partial_cmp(&self.distance)
    }
}

impl<W: Ord> Ord for State<W> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.distance.cmp(&self.distance)
    }
}

#[derive(Debug, Clone)]
struct DijkstraIndexedResult<W> {
    distances: Vec<W>,
    next: Vec<Option<usize>>,
}

/// 在编号为 0..n-1 的图上运行 Dijkstra 算法
///
/// 使用 `W::from(i32::MAX)` 作为无穷大。
fn dijkstra_indexed<W>(n: usize, edges: &[(usize, usize, W)], source: usize) -> DijkstraIndexedResult<W>
where
    W: Clone + Ord + std::ops::Add<Output = W> + Default + From<i32>,
{
    let inf = W::from(i32::MAX);
    let mut adj = vec![Vec::new(); n];
    for (u, v, w) in edges.iter() {
        adj[*u].push((*v, w.clone()));
    }

    let mut distances = vec![inf.clone(); n];
    let mut next = vec![None; n];
    let mut visited = vec![false; n];

    distances[source] = W::default();

    let mut heap = BinaryHeap::new();
    heap.push(State {
        distance: W::default(),
        vertex: source,
    });

    while let Some(State { distance, vertex: u }) = heap.pop() {
        if visited[u] {
            continue;
        }
        if distance > distances[u] {
            continue;
        }
        visited[u] = true;

        for (v, w) in &adj[u] {
            if visited[*v] {
                continue;
            }
            let new_dist = distance.clone() + w.clone();
            if new_dist < distances[*v] {
                distances[*v] = new_dist.clone();
                next[*v] = if u == source { Some(*v) } else { next[u] };
                heap.push(State {
                    distance: new_dist,
                    vertex: *v,
                });
            }
        }
    }

    DijkstraIndexedResult { distances, next }
}

/// Johnson 全对最短路径算法
///
/// # 算法说明
///
/// 1. 添加超级源点 s，向所有顶点连一条权重为 0 的边。
/// 2. 运行 Bellman-Ford 算法，计算 h[v] = δ(s, v)。
/// 3. 若存在负权环，返回错误。
/// 4. 对每条边 (u, v) 重新赋权：ŵ(u, v) = w(u, v) + h[u] - h[v]。
/// 5. 对每个顶点 u 运行 Dijkstra 算法（使用非负权重 ŵ）。
/// 6. 将距离还原：d(u, v) = d̂(u, v) - h[u] + h[v]。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V·E + V·E·log V) = O(V·E·log V)（使用二叉堆）
/// - **空间复杂度**：O(V²)
///
/// # 参数
///
/// * `n` - 顶点数量（编号为 0 到 n-1）
/// * `edges` - 边列表，每条边为 (u, v, weight)
///
/// # 返回值
///
/// 成功时返回 `JohnsonResult`，失败时返回 `AlgorithmError::GraphError`（存在负权环）
///
/// # 示例
///
/// ```
/// use formal_algorithms::johnson::johnson;
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
/// let result = johnson(4, &edges).unwrap();
/// assert_eq!(result.dist[0][2], 5); // 0->1->2 = 3+2 = 5
/// assert_eq!(result.dist[1][3], 3); // 1->2->3 = 2+1 = 3
/// ```
pub fn johnson<W>(n: usize, edges: &[(usize, usize, W)]) -> Result<JohnsonResult<W>, AlgorithmError>
where
    W: Clone + Ord + std::ops::Add<Output = W> + std::ops::Sub<Output = W> + Default + From<i32>,
{
    let inf = W::from(i32::MAX);

    // 1. 添加超级源点，运行 Bellman-Ford
    let s = n;
    let mut bf_edges: Vec<(usize, usize, W)> = edges.to_vec();
    for v in 0..n {
        bf_edges.push((s, v, W::default()));
    }

    let bf_result = bellman_ford(&bf_edges, s)?;

    // 2. 计算势能 h
    let mut h = vec![inf.clone(); n];
    for v in 0..n {
        h[v] = bf_result.distances.get(&v).cloned().unwrap_or_else(|| inf.clone());
    }

    // 3. 重新赋权
    let mut reweighted: Vec<(usize, usize, W)> = Vec::with_capacity(edges.len());
    for (u, v, w) in edges.iter() {
        let hw = w.clone() + h[*u].clone() - h[*v].clone();
        reweighted.push((*u, *v, hw));
    }

    // 4. 对每个顶点运行 Dijkstra
    let mut dist = vec![vec![inf.clone(); n]; n];
    let mut next = vec![vec![None; n]; n];

    for u in 0..n {
        let d_result = dijkstra_indexed(n, &reweighted, u);
        for v in 0..n {
            if u == v {
                dist[u][v] = W::default();
                continue;
            }
            let dv = d_result.distances[v].clone();
            if dv != inf {
                let original = dv - h[u].clone() + h[v].clone();
                dist[u][v] = original;
                next[u][v] = d_result.next[v];
            }
        }
    }

    Ok(JohnsonResult { dist, next })
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
        let result = johnson(4, &edges).unwrap();
        assert_eq!(result.dist[0][2], 5);
        assert_eq!(result.dist[1][3], 3);
        assert_eq!(result.dist[3][2], 7);
    }

    #[test]
    fn test_negative_edges() {
        let edges = vec![
            (0, 1, -5),
            (0, 2, 2),
            (1, 2, 4),
            (2, 3, 1),
            (3, 1, -3),
        ];
        let result = johnson(4, &edges).unwrap();
        assert_eq!(result.dist[0][1], -5);
        assert_eq!(result.dist[0][3], 0); // 0->1->2->3 = -5+4+1 = 0
        assert_eq!(result.dist[3][1], -3);
    }

    #[test]
    fn test_negative_cycle() {
        let edges = vec![(0, 1, 1), (1, 2, -3), (2, 0, 1)];
        let result = johnson(3, &edges);
        assert!(matches!(result, Err(AlgorithmError::GraphError(_))));
    }

    #[test]
    fn test_disconnected() {
        let edges = vec![(0, 1, 5)];
        let result = johnson(3, &edges).unwrap();
        assert_eq!(result.dist[0][1], 5);
        assert_eq!(result.dist[0][2], i32::MAX);
        assert!(result.path(0, 2).is_none());
    }

    #[test]
    fn test_path_reconstruction() {
        let edges = vec![(0, 1, 3), (1, 2, 2), (2, 3, 1)];
        let result = johnson(4, &edges).unwrap();
        let path = result.path(0, 3).unwrap();
        assert_eq!(path, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_same_vertex_path() {
        let result: JohnsonResult<i32> = johnson(2, &[]).unwrap();
        assert_eq!(result.path(0, 0), Some(vec![0]));
    }
}
