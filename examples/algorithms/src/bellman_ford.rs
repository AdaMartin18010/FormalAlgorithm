//! Bellman-Ford 单源最短路径算法
//!
//! 支持负权边，可检测从源点可达的负权环。
//! 对标: CLRS Chapter 24.1

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::AlgorithmError;

/// Bellman-Ford 算法结果
#[derive(Debug, Clone)]
pub struct BellmanFordResult<V, W> {
    /// 从源点到各顶点的最短距离
    pub distances: HashMap<V, W>,
    /// 前驱节点，用于重建路径
    pub predecessors: HashMap<V, V>,
}

impl<V, W> BellmanFordResult<V, W> {
    /// 获取到目标顶点的距离
    pub fn distance_to(&self, vertex: &V) -> Option<&W>
    where
        V: Eq + Hash,
    {
        self.distances.get(vertex)
    }

    /// 重建从源点到目标顶点的路径
    ///
    /// # 注意
    /// 若目标顶点存在于图中但不可达，返回仅包含该顶点的单元素路径。
    pub fn path_to(&self, target: &V) -> Option<Vec<V>>
    where
        V: Clone + Eq + Hash,
    {
        if !self.distances.contains_key(target) {
            return None;
        }
        let mut path = vec![];
        let mut current = target.clone();
        path.push(current.clone());
        while let Some(prev) = self.predecessors.get(&current) {
            path.push(prev.clone());
            current = prev.clone();
        }
        path.reverse();
        Some(path)
    }
}

/// Bellman-Ford 单源最短路径算法
///
/// # 算法说明
///
/// 1. 初始化：源点距离为 0，其他点为 ∞
/// 2. 对每条边进行 |V|-1 轮松弛
/// 3. 再进行一轮松弛，若还能更新则存在负权环
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V·E)
/// - **空间复杂度**：O(V)
///
/// # 参数
///
/// * `edges` - 图的边列表，每条边包含 (from, to, weight)
/// * `source` - 源点
///
/// # 返回值
///
/// 成功时返回 `BellmanFordResult`，失败时返回 `AlgorithmError::GraphError`（存在负权环）
///
/// # 示例
///
/// ```
/// use formal_algorithms::bellman_ford::bellman_ford;
///
/// let edges = vec![
///     (0, 1, -1),
///     (0, 2, 4),
///     (1, 2, 3),
///     (1, 3, 2),
///     (1, 4, 2),
///     (3, 2, 5),
///     (3, 1, 1),
///     (4, 3, -3),
/// ];
///
/// let result = bellman_ford(&edges, 0).unwrap();
/// assert_eq!(result.distances.get(&3), Some(&-2)); // 0->1->4->3 = -1+2-3 = -2
/// ```
pub fn bellman_ford<V, W>(
    edges: &[(V, V, W)],
    source: V,
) -> Result<BellmanFordResult<V, W>, AlgorithmError>
where
    V: Clone + Eq + Hash,
    W: Clone + Ord + std::ops::Add<Output = W> + Default + From<i32>,
{
    let mut vertices = HashSet::new();
    vertices.insert(source.clone());
    for (u, v, _) in edges.iter() {
        vertices.insert(u.clone());
        vertices.insert(v.clone());
    }
    let n = vertices.len();

    let inf = W::from(i32::MAX);
    let mut distances: HashMap<V, W> = HashMap::new();
    let mut predecessors: HashMap<V, V> = HashMap::new();

    for v in &vertices {
        if *v == source {
            distances.insert(v.clone(), W::default());
        } else {
            distances.insert(v.clone(), inf.clone());
        }
    }

    // 松弛 |V|-1 次
    for _ in 1..n {
        let mut updated = false;
        for (u, v, w) in edges.iter() {
            let du = distances.get(u).cloned().unwrap_or_else(|| inf.clone());
            if du == inf {
                continue;
            }
            let dv = distances.get(v).cloned().unwrap_or_else(|| inf.clone());
            let new_d = du.clone() + w.clone();
            if new_d < dv {
                distances.insert(v.clone(), new_d);
                predecessors.insert(v.clone(), u.clone());
                updated = true;
            }
        }
        if !updated {
            break;
        }
    }

    // 负权环检测
    for (u, v, w) in edges.iter() {
        let du = distances.get(u).cloned().unwrap_or_else(|| inf.clone());
        if du == inf {
            continue;
        }
        let dv = distances.get(v).cloned().unwrap_or_else(|| inf.clone());
        let new_d = du.clone() + w.clone();
        if new_d < dv {
            return Err(AlgorithmError::GraphError(
                "Negative-weight cycle detected".to_string(),
            ));
        }
    }

    Ok(BellmanFordResult {
        distances,
        predecessors,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let edges = vec![
            (0, 1, -1),
            (0, 2, 4),
            (1, 2, 3),
            (1, 3, 2),
            (1, 4, 2),
            (3, 2, 5),
            (3, 1, 1),
            (4, 3, -3),
        ];
        let result = bellman_ford(&edges, 0).unwrap();
        assert_eq!(result.distances.get(&0), Some(&0));
        assert_eq!(result.distances.get(&1), Some(&-1));
        assert_eq!(result.distances.get(&2), Some(&2));
        assert_eq!(result.distances.get(&3), Some(&-2));
        assert_eq!(result.distances.get(&4), Some(&1));
    }

    #[test]
    fn test_negative_cycle() {
        let edges = vec![(0, 1, 1), (1, 2, -1), (2, 0, -1)];
        let result = bellman_ford(&edges, 0);
        assert!(matches!(result, Err(AlgorithmError::GraphError(_))));
    }

    #[test]
    fn test_unreachable() {
        let edges = vec![(0, 1, 5)];
        let result = bellman_ford(&edges, 0).unwrap();
        assert_eq!(result.distances.get(&1), Some(&5));
        // 顶点 2 不在图中，故 distances 中不包含该键
        assert_eq!(result.distances.get(&2), None);
    }

    #[test]
    fn test_path_reconstruction() {
        let edges = vec![(0, 1, -1), (1, 4, 2), (4, 3, -3)];
        let result = bellman_ford(&edges, 0).unwrap();
        let path = result.path_to(&3).unwrap();
        assert_eq!(path, vec![0, 1, 4, 3]);
    }

    #[test]
    fn test_single_vertex() {
        let edges: Vec<(char, char, i32)> = vec![];
        let result = bellman_ford(&edges, 'A').unwrap();
        assert_eq!(result.distances.get(&'A'), Some(&0));
        assert_eq!(result.distances.len(), 1);
    }
}
