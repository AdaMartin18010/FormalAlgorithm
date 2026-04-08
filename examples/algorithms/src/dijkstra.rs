//! Dijkstra最短路径算法实现
//!
//! Dijkstra算法用于在带权有向图中找到从单一源点到所有其他顶点的最短路径。
//! 要求所有边的权重为非负数。

use crate::{AlgorithmError, SearchResult};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::hash::Hash;

/// 图边结构
#[derive(Debug, Clone, PartialEq)]
pub struct Edge<V, W> {
    /// 起始顶点
    pub from: V,
    /// 目标顶点
    pub to: V,
    /// 边权重
    pub weight: W,
}

impl<V, W> Edge<V, W> {
    /// 创建新边
    pub fn new(from: V, to: V, weight: W) -> Self {
        Edge { from, to, weight }
    }
}

/// Dijkstra算法状态
#[derive(Debug)]
pub struct DijkstraResult<V, W> {
    /// 从源点到各顶点的最短距离
    pub distances: HashMap<V, W>,
    /// 前驱节点，用于重建路径
    pub predecessors: HashMap<V, V>,
}

impl<V, W> DijkstraResult<V, W> {
    /// 获取到目标顶点的距离
    pub fn distance_to(&self, vertex: &V) -> Option<&W>
    where
        V: Eq + Hash,
    {
        self.distances.get(vertex)
    }

    /// 重建从源点到目标顶点的路径
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

/// 优先队列中的状态
#[derive(Debug, Clone)]
struct State<V, W> {
    /// 当前距离
    distance: W,
    /// 当前顶点
    vertex: V,
}

impl<V, W: PartialEq> PartialEq for State<V, W> {
    fn eq(&self, other: &Self) -> bool {
        self.distance == other.distance
    }
}

impl<V, W: Eq> Eq for State<V, W> {}

impl<V, W: PartialOrd> PartialOrd for State<V, W> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 注意：BinaryHeap是最大堆，所以需要反向比较
        other.distance.partial_cmp(&self.distance)
    }
}

impl<V, W: Ord> Ord for State<V, W> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.distance.cmp(&self.distance)
    }
}

/// Dijkstra最短路径算法
///
/// # 算法说明
///
/// Dijkstra算法是一种贪心算法，用于求解单源最短路径问题：
/// 1. 初始化：源点距离为0，其他点为无穷大
/// 2. 选择距离最小的未访问顶点
/// 3. 更新该顶点的所有邻接顶点的距离
/// 4. 重复步骤2-3直到所有顶点都被访问
///
/// # 复杂度分析
///
/// - **时间复杂度**：O((V+E) log V)
///   - 使用优先队列实现
///   - 每个顶点入队出队一次：O(V log V)
///   - 每条边可能被松弛一次：O(E log V)
/// - **空间复杂度**：O(V)
///   - 存储距离和前驱节点
///
/// # 参数
///
/// * `edges` - 图的边列表，每条边包含 (from, to, weight)
/// * `source` - 源点
///
/// # 返回值
///
/// 返回 `DijkstraResult`，包含：
/// - `distances`: 从源点到各顶点的最短距离映射
/// - `predecessors`: 前驱节点映射，用于重建路径
///
/// # 示例
///
/// ```
/// use formal_algorithms::dijkstra;
///
/// let edges = vec![
///     ('A', 'B', 4),
///     ('A', 'C', 2),
///     ('B', 'C', 1),
///     ('B', 'D', 5),
///     ('C', 'D', 8),
///     ('C', 'E', 10),
///     ('D', 'E', 2),
///     ('D', 'F', 6),
///     ('E', 'F', 3),
/// ];
///
/// let result = dijkstra(&edges, 'A');
/// assert_eq!(result.distances.get(&'D'), Some(&9)); // A->C->B->D = 2+1+5 = 8
/// ```
///
/// # 注意事项
///
/// * 图中不能包含负权边，否则算法结果不正确
/// * 使用 `get_path` 方法可以重建最短路径
pub fn dijkstra<V, W>(edges: &[(V, V, W)], source: V) -> DijkstraResult<V, W>
where
    V: Clone + Eq + Hash,
    W: Clone + Ord + std::ops::Add<Output = W> + From<u8> + Default,
{
    // 构建邻接表
    let mut adjacency_list: HashMap<V, Vec<(V, W)>> = HashMap::new();
    let mut vertices: HashSet<V> = HashSet::new();

    for (from, to, weight) in edges.iter() {
        adjacency_list
            .entry(from.clone())
            .or_default()
            .push((to.clone(), weight.clone()));
        vertices.insert(from.clone());
        vertices.insert(to.clone());
    }

    // 初始化距离和前驱
    let mut distances: HashMap<V, W> = HashMap::new();
    let mut predecessors: HashMap<V, V> = HashMap::new();
    let mut visited: HashSet<V> = HashSet::new();

    // 设置源点距离为0，其他为无穷大（用最大值表示）
    for vertex in &vertices {
        if *vertex == source {
            distances.insert(vertex.clone(), W::default());
        } else {
            // 使用一个较大的值作为无穷大
            distances.insert(vertex.clone(), W::from(255u8));
        }
    }

    // 优先队列
    let mut heap = BinaryHeap::new();
    heap.push(State {
        distance: W::default(),
        vertex: source,
    });

    while let Some(State { distance, vertex }) = heap.pop() {
        // 如果已经访问过，跳过
        if visited.contains(&vertex) {
            continue;
        }

        // 如果当前距离已经大于已知最短距离，跳过
        if let Some(&known_dist) = distances.get(&vertex) {
            if distance > known_dist {
                continue;
            }
        }

        visited.insert(vertex.clone());

        // 松弛操作
        if let Some(neighbors) = adjacency_list.get(&vertex) {
            for (neighbor, weight) in neighbors {
                if visited.contains(neighbor) {
                    continue;
                }

                let new_distance = distance.clone() + weight.clone();
                let current_distance = distances.get(neighbor).cloned().unwrap_or_else(|| W::from(255u8));

                if new_distance < current_distance {
                    distances.insert(neighbor.clone(), new_distance.clone());
                    predecessors.insert(neighbor.clone(), vertex.clone());
                    heap.push(State {
                        distance: new_distance,
                        vertex: neighbor.clone(),
                    });
                }
            }
        }
    }

    DijkstraResult {
        distances,
        predecessors,
    }
}

/// 使用邻接表表示的Dijkstra算法
///
/// 适用于频繁查询的场景，避免重复构建邻接表
///
/// # 参数
///
/// * `graph` - 邻接表，从顶点到 (邻居, 权重) 列表的映射
/// * `source` - 源点
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::dijkstra::dijkstra_with_graph;
///
/// let mut graph: HashMap<char, Vec<(char, i32)>> = HashMap::new();
/// graph.insert('A', vec![('B', 4), ('C', 2)]);
/// graph.insert('B', vec![('C', 1), ('D', 5)]);
/// graph.insert('C', vec![('D', 8)]);
///
/// let result = dijkstra_with_graph(&graph, 'A');
/// assert_eq!(result.distances.get(&'D'), Some(&10));
/// ```
pub fn dijkstra_with_graph<V, W>(graph: &HashMap<V, Vec<(V, W)>>, source: V) -> DijkstraResult<V, W>
where
    V: Clone + Eq + Hash,
    W: Clone + Ord + std::ops::Add<Output = W> + From<u8> + Default,
{
    let mut distances: HashMap<V, W> = HashMap::new();
    let mut predecessors: HashMap<V, V> = HashMap::new();
    let mut visited: HashSet<V> = HashSet::new();

    // 收集所有顶点
    let mut vertices: HashSet<V> = HashSet::new();
    vertices.insert(source.clone());
    for (v, neighbors) in graph.iter() {
        vertices.insert(v.clone());
        for (n, _) in neighbors {
            vertices.insert(n.clone());
        }
    }

    // 初始化距离
    for vertex in &vertices {
        if *vertex == source {
            distances.insert(vertex.clone(), W::default());
        } else {
            distances.insert(vertex.clone(), W::from(255u8));
        }
    }

    let mut heap = BinaryHeap::new();
    heap.push(State {
        distance: W::default(),
        vertex: source,
    });

    while let Some(State { distance, vertex }) = heap.pop() {
        if visited.contains(&vertex) {
            continue;
        }

        if let Some(&known_dist) = distances.get(&vertex) {
            if distance > known_dist {
                continue;
            }
        }

        visited.insert(vertex.clone());

        if let Some(neighbors) = graph.get(&vertex) {
            for (neighbor, weight) in neighbors {
                if visited.contains(neighbor) {
                    continue;
                }

                let new_distance = distance.clone() + weight.clone();
                let current_distance = distances.get(neighbor).cloned().unwrap_or_else(|| W::from(255u8));

                if new_distance < current_distance {
                    distances.insert(neighbor.clone(), new_distance.clone());
                    predecessors.insert(neighbor.clone(), vertex.clone());
                    heap.push(State {
                        distance: new_distance,
                        vertex: neighbor.clone(),
                    });
                }
            }
        }
    }

    DijkstraResult {
        distances,
        predecessors,
    }
}

/// 检查图中是否存在负权边
///
/// Dijkstra算法要求所有边的权重非负
pub fn has_negative_edge<V, W>(edges: &[(V, V, W)]) -> bool
where
    W: PartialOrd + Default,
{
    edges.iter().any(|(_, _, w)| *w < W::default())
}

/// 获取最短路径的字符串表示
///
/// 将路径格式化为 "A -> B -> C" 的形式
pub fn format_path<V: std::fmt::Display>(path: &[V]) -> String {
    path.iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(" -> ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_dijkstra() {
        let edges = vec![
            ('A', 'B', 4),
            ('A', 'C', 2),
            ('B', 'C', 1),
            ('B', 'D', 5),
            ('C', 'D', 8),
        ];

        let result = dijkstra(&edges, 'A');
        
        assert_eq!(result.distances.get(&'A'), Some(&0));
        assert_eq!(result.distances.get(&'B'), Some(&4));
        assert_eq!(result.distances.get(&'C'), Some(&2));
        assert_eq!(result.distances.get(&'D'), Some(&9));
    }

    #[test]
    fn test_path_reconstruction() {
        let edges = vec![
            ('A', 'B', 4),
            ('A', 'C', 2),
            ('B', 'C', 1),
            ('B', 'D', 5),
            ('C', 'D', 8),
        ];

        let result = dijkstra(&edges, 'A');
        let path = result.path_to(&'D').unwrap();
        
        assert_eq!(path, vec!['A', 'B', 'D']);
    }

    #[test]
    fn test_disconnected_graph() {
        let edges = vec![
            ('A', 'B', 1),
            ('C', 'D', 1),
        ];

        let result = dijkstra(&edges, 'A');
        
        assert_eq!(result.distances.get(&'A'), Some(&0));
        assert_eq!(result.distances.get(&'B'), Some(&1));
        // C和D不可达，距离保持为"无穷大"
        assert!(result.distances.get(&'C').is_some());
        assert!(result.path_to(&'C').is_none());
    }

    #[test]
    fn test_single_vertex() {
        let edges: Vec<(char, char, i32)> = vec![];
        let result = dijkstra(&edges, 'A');
        
        assert_eq!(result.distances.get(&'A'), Some(&0));
    }

    #[test]
    fn test_triangle_graph() {
        let edges = vec![
            ('A', 'B', 1),
            ('B', 'C', 1),
            ('A', 'C', 3),
        ];

        let result = dijkstra(&edges, 'A');
        
        assert_eq!(result.distances.get(&'C'), Some(&2)); // A->B->C = 2 < 3
    }

    #[test]
    fn test_with_graph() {
        let mut graph: HashMap<char, Vec<(char, i32)>> = HashMap::new();
        graph.insert('A', vec![('B', 4), ('C', 2)]);
        graph.insert('B', vec![('C', 1), ('D', 5)]);
        graph.insert('C', vec![('D', 8)]);

        let result = dijkstra_with_graph(&graph, 'A');
        
        assert_eq!(result.distances.get(&'D'), Some(&9));
    }

    #[test]
    fn test_integer_weights() {
        let edges = vec![
            (0, 1, 10),
            (0, 2, 3),
            (1, 3, 2),
            (2, 1, 4),
            (2, 3, 8),
            (2, 4, 2),
            (3, 4, 5),
        ];

        let result = dijkstra(&edges, 0);
        
        assert_eq!(result.distances.get(&0), Some(&0));
        assert_eq!(result.distances.get(&1), Some(&7));  // 0->2->1
        assert_eq!(result.distances.get(&3), Some(&9));  // 0->2->1->3
    }

    #[test]
    fn test_path_to_unreachable() {
        let edges = vec![
            ('A', 'B', 1),
        ];

        let result = dijkstra(&edges, 'A');
        
        assert!(result.path_to(&'C').is_none());
    }

    #[test]
    fn test_format_path() {
        let path = vec!['A', 'B', 'C', 'D'];
        assert_eq!(format_path(&path), "A -> B -> C -> D");
    }
}
