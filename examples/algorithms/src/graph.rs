//! # 图算法 / Graph Algorithms
//!
//! 实现经典图算法及其形式化规范。

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap};

/// 图的边 / Graph Edge
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub to: usize,
    pub weight: usize,
}

/// 优先队列中的节点 / Priority Queue Node
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct State {
    cost: usize,
    position: usize,
}

// 为最小堆实现Ord trait
impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost)
            .then_with(|| self.position.cmp(&other.position))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Dijkstra最短路径算法 / Dijkstra's Shortest Path Algorithm
///
/// # 形式化定义 / Formal Definition
///
/// 给定带权图 G = (V, E) 和源节点 s ∈ V，找到从 s 到所有其他节点的最短路径。
///
/// ## 算法思想 / Algorithm Idea
///
/// 1. 初始化：源节点距离为0，其他节点距离为∞
/// 2. 维护优先队列Q，按距离排序
/// 3. 重复直到Q为空：
///    - 提取距离最小的节点u
///    - 对u的每个邻居v进行松弛操作
///    - 如果通过u到v的距离更短，更新v的距离
///
/// ## 松弛操作 / Relaxation
///
/// 对于边 (u, v)，如果 dist[u] + weight(u, v) < dist[v]，则：
/// ```text
/// dist[v] := dist[u] + weight(u, v)
/// predecessor[v] := u
/// ```
///
/// ## 正确性 / Correctness
///
/// **循环不变量**: 对于所有已确定最短路径的节点u，dist[u]是从源点到u的真实最短距离。
///
/// **证明草图**:
/// - 初始时，只有源节点s确定，dist[s] = 0正确
/// - 每次选择dist最小的未确定节点u，由于所有权重非负，
///   不存在通过未确定节点到u的更短路径
/// - 因此u的dist值是最终的最短距离
///
/// ## 前提条件 / Precondition
/// - 所有边的权重必须非负
///
/// ## 时间复杂度 / Time Complexity
/// - O((V + E) log V) - 使用二叉堆
/// - O(V² + E) - 使用普通数组
/// - O(V log V + E) - 使用斐波那契堆
///
/// ## 空间复杂度 / Space Complexity
/// - O(V) - 距离数组和优先队列
///
/// # 参考文献 / References
/// - [CLRS2009] Cormen et al., "Introduction to Algorithms", 第3版, 第24.3节
/// - [Dijkstra1959] E. W. Dijkstra, "A Note on Two Problems in Connexion with Graphs"
/// - 对应文档: `docs/09-算法理论/03-图论算法/01-最短路径.md`
///
/// # Examples
///
/// ```
/// use algorithms::graph::{dijkstra, Edge};
/// use std::collections::HashMap;
///
/// let mut graph: HashMap<usize, Vec<Edge>> = HashMap::new();
/// graph.insert(0, vec![Edge { to: 1, weight: 4 }, Edge { to: 2, weight: 1 }]);
/// graph.insert(1, vec![Edge { to: 3, weight: 1 }]);
/// graph.insert(2, vec![Edge { to: 1, weight: 2 }, Edge { to: 3, weight: 5 }]);
/// graph.insert(3, vec![]);
///
/// let distances = dijkstra(&graph, 0, 4);
/// assert_eq!(distances[0], 0);
/// assert_eq!(distances[1], 3);
/// assert_eq!(distances[2], 1);
/// assert_eq!(distances[3], 4);
/// ```
pub fn dijkstra(
    graph: &HashMap<usize, Vec<Edge>>,
    start: usize,
    num_nodes: usize,
) -> Vec<Option<usize>> {
    // 初始化距离数组
    let mut dist = vec![None; num_nodes];
    dist[start] = Some(0);
    
    // 优先队列（最小堆）
    let mut heap = BinaryHeap::new();
    heap.push(State { cost: 0, position: start });
    
    // 主循环
    while let Some(State { cost, position }) = heap.pop() {
        // 如果已经找到更短的路径，跳过
        if let Some(current_dist) = dist[position] {
            if cost > current_dist {
                continue;
            }
        }
        
        // 检查所有邻居
        if let Some(edges) = graph.get(&position) {
            for edge in edges {
                let next_cost = cost + edge.weight;
                
                // 松弛操作
                let should_update = match dist[edge.to] {
                    None => true,
                    Some(current) => next_cost < current,
                };
                
                if should_update {
                    dist[edge.to] = Some(next_cost);
                    heap.push(State {
                        cost: next_cost,
                        position: edge.to,
                    });
                }
            }
        }
    }
    
    dist
}

/// Dijkstra算法（带路径重构）/ Dijkstra with Path Reconstruction
///
/// 返回最短距离和前驱节点，可用于重构完整路径。
///
/// # Examples
///
/// ```
/// use algorithms::graph::{dijkstra_with_path, Edge, reconstruct_path};
/// use std::collections::HashMap;
///
/// let mut graph: HashMap<usize, Vec<Edge>> = HashMap::new();
/// graph.insert(0, vec![Edge { to: 1, weight: 4 }, Edge { to: 2, weight: 1 }]);
/// graph.insert(1, vec![Edge { to: 3, weight: 1 }]);
/// graph.insert(2, vec![Edge { to: 1, weight: 2 }, Edge { to: 3, weight: 5 }]);
/// graph.insert(3, vec![]);
///
/// let (distances, predecessors) = dijkstra_with_path(&graph, 0, 4);
/// let path = reconstruct_path(&predecessors, 3);
/// assert_eq!(path, vec![0, 2, 1, 3]);
/// ```
pub fn dijkstra_with_path(
    graph: &HashMap<usize, Vec<Edge>>,
    start: usize,
    num_nodes: usize,
) -> (Vec<Option<usize>>, Vec<Option<usize>>) {
    let mut dist = vec![None; num_nodes];
    let mut predecessor = vec![None; num_nodes];
    dist[start] = Some(0);
    
    let mut heap = BinaryHeap::new();
    heap.push(State { cost: 0, position: start });
    
    while let Some(State { cost, position }) = heap.pop() {
        if let Some(current_dist) = dist[position] {
            if cost > current_dist {
                continue;
            }
        }
        
        if let Some(edges) = graph.get(&position) {
            for edge in edges {
                let next_cost = cost + edge.weight;
                
                let should_update = match dist[edge.to] {
                    None => true,
                    Some(current) => next_cost < current,
                };
                
                if should_update {
                    dist[edge.to] = Some(next_cost);
                    predecessor[edge.to] = Some(position);
                    heap.push(State {
                        cost: next_cost,
                        position: edge.to,
                    });
                }
            }
        }
    }
    
    (dist, predecessor)
}

/// 重构从源点到目标的路径 / Reconstruct Path
///
/// # Examples
///
/// ```
/// use algorithms::graph::reconstruct_path;
///
/// let predecessors = vec![None, Some(0), Some(0), Some(1)];
/// let path = reconstruct_path(&predecessors, 3);
/// assert_eq!(path, vec![0, 1, 3]);
/// ```
pub fn reconstruct_path(predecessors: &[Option<usize>], target: usize) -> Vec<usize> {
    let mut path = Vec::new();
    let mut current = Some(target);
    
    while let Some(node) = current {
        path.push(node);
        current = predecessors[node];
    }
    
    path.reverse();
    path
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn create_test_graph() -> HashMap<usize, Vec<Edge>> {
        let mut graph = HashMap::new();
        graph.insert(0, vec![Edge { to: 1, weight: 4 }, Edge { to: 2, weight: 1 }]);
        graph.insert(1, vec![Edge { to: 3, weight: 1 }]);
        graph.insert(2, vec![Edge { to: 1, weight: 2 }, Edge { to: 3, weight: 5 }]);
        graph.insert(3, vec![]);
        graph
    }
    
    #[test]
    fn test_dijkstra_basic() {
        let graph = create_test_graph();
        let distances = dijkstra(&graph, 0, 4);
        
        assert_eq!(distances[0], Some(0));
        assert_eq!(distances[1], Some(3));
        assert_eq!(distances[2], Some(1));
        assert_eq!(distances[3], Some(4));
    }
    
    #[test]
    fn test_dijkstra_unreachable() {
        let mut graph = HashMap::new();
        graph.insert(0, vec![Edge { to: 1, weight: 1 }]);
        graph.insert(1, vec![]);
        graph.insert(2, vec![Edge { to: 3, weight: 1 }]);
        graph.insert(3, vec![]);
        
        let distances = dijkstra(&graph, 0, 4);
        assert_eq!(distances[0], Some(0));
        assert_eq!(distances[1], Some(1));
        assert_eq!(distances[2], None); // 不可达
        assert_eq!(distances[3], None); // 不可达
    }
    
    #[test]
    fn test_dijkstra_single_node() {
        let graph = HashMap::new();
        let distances = dijkstra(&graph, 0, 1);
        assert_eq!(distances[0], Some(0));
    }
    
    #[test]
    fn test_dijkstra_with_path() {
        let graph = create_test_graph();
        let (distances, predecessors) = dijkstra_with_path(&graph, 0, 4);
        
        assert_eq!(distances[3], Some(4));
        let path = reconstruct_path(&predecessors, 3);
        assert_eq!(path, vec![0, 2, 1, 3]);
    }
    
    #[test]
    fn test_path_reconstruction() {
        let predecessors = vec![None, Some(0), Some(0), Some(1)];
        
        let path0 = reconstruct_path(&predecessors, 0);
        assert_eq!(path0, vec![0]);
        
        let path3 = reconstruct_path(&predecessors, 3);
        assert_eq!(path3, vec![0, 1, 3]);
    }
}

