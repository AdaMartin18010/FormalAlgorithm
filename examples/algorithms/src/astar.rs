//! A* (A-Star) 搜索算法实现
//!
//! A* 搜索是一种启发式搜索算法，广泛用于路径规划和图遍历。
//! 它通过引入启发式函数 h(n) 来估计从节点 n 到目标的最小代价，
//! 从而在大多数情况下比 Dijkstra 算法和纯 BFS 更高效。
//!
//! 对标: CLRS 未独立成章，但为 MIT 6.006、Stanford CS161、CMU 15-451 等国际课程标配内容。
//!
//! ## 核心性质
//!
//! - **可采纳性 (Admissibility)**：若启发式函数 h(n) 永不高估实际代价，
//!   则 A* 保证找到最优解。
//! - **一致性 (Consistency)**：若 h(n) ≤ c(n, n') + h(n') 对所有边成立，
//!   则 A* 的行为类似于 Dijkstra，且保证最优性。
//! - **完备性**：在有限图或有限分支因子的无限图中，若存在解则 A* 必能找到。
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：O(b^d)，其中 b 为分支因子，d 为解深度；
//!   实际运行时间高度依赖启发式质量。良好启发式可接近 O(E)。
//! - **空间复杂度**：O(V) —— 需存储已访问和待探索节点集合。
//!
//! ## 与 Dijkstra / BFS 的关系
//!
//! | 算法 | f(n) | 当 h(n)=0 | 当 h(n)=实际距离 |
//! |------|------|----------|----------------|
//! | Dijkstra | g(n) | 等价 | — |
//! | BFS | g(n)（无权图） | 等价（无权图） | — |
//! | A* | g(n) + h(n) | 退化为 Dijkstra | 直接沿最优路径前进 |
//!
//! 其中 g(n) 为从起点到 n 的实际代价。

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::hash::Hash;

/// A* 搜索结果
#[derive(Debug, Clone)]
pub struct AStarResult<V> {
    /// 从起点到目标的最短路径（若存在）
    pub path: Option<Vec<V>>,
    /// 路径总代价（若存在）
    pub cost: Option<f64>,
    /// 实际访问的节点数（用于评估算法效率）
    pub nodes_expanded: usize,
}

impl<V> AStarResult<V> {
    /// 创建无路径的结果
    pub fn failure(nodes_expanded: usize) -> Self {
        AStarResult {
            path: None,
            cost: None,
            nodes_expanded,
        }
    }
}

/// 优先队列中的节点状态
#[derive(Debug, Clone)]
struct State<V> {
    /// f(n) = g(n) + h(n)，优先级键值
    f_score: f64,
    /// g(n)，从起点到当前节点的实际代价
    g_score: f64,
    /// 当前节点
    vertex: V,
}

impl<V: PartialEq> PartialEq for State<V> {
    fn eq(&self, other: &Self) -> bool {
        self.f_score == other.f_score
    }
}

impl<V: PartialEq> Eq for State<V> {}

impl<V: PartialEq> PartialOrd for State<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // BinaryHeap 是最大堆，因此我们反转比较逻辑以实现最小堆
        other.f_score.partial_cmp(&self.f_score)
    }
}

impl<V: PartialEq> Ord for State<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

/// A* 搜索算法
///
/// # 参数
///
/// * `start` - 起始节点
/// * `goal` - 目标节点（用于终止判断）
/// * `neighbors` - 返回某节点的所有邻居及边代价的函数
/// * `heuristic` - 启发式函数 h(n)，估计从节点 n 到目标的代价
/// * `is_goal` - 判断节点是否为目标
///
/// # 返回值
///
/// 返回 `AStarResult`，包含最短路径（若存在）、代价和访问节点数。
///
/// # 类型参数
///
/// * `V` - 节点类型，需实现 `Clone + Eq + Hash`
/// * `N` - 邻居迭代器类型
/// * `FN` - 邻居函数类型
/// * `FH` - 启发式函数类型
/// * `FG` - 目标判断函数类型
///
/// # 示例
///
/// ```
/// use formal_algorithms::astar::astar;
///
/// // 在网格中搜索从 (0,0) 到 (2,2) 的最短路径（曼哈顿移动）
/// let start = (0i32, 0i32);
/// let goal = (2i32, 2i32);
///
/// let result = astar(
///     &start,
///     |v| {
///         let (x, y) = *v;
///         vec![
///             ((x + 1, y), 1.0),
///             ((x - 1, y), 1.0),
///             ((x, y + 1), 1.0),
///             ((x, y - 1), 1.0),
///         ]
///     },
///     |v| {
///         let (x, y) = *v;
///         ((x - goal.0).abs() + (y - goal.1).abs()) as f64
///     },
///     |v| *v == goal,
/// );
///
/// assert!(result.path.is_some());
/// assert_eq!(result.cost, Some(4.0));
/// ```
pub fn astar<V, N, FN, FH, FG>(
    start: &V,
    mut neighbors: FN,
    mut heuristic: FH,
    mut is_goal: FG,
) -> AStarResult<V>
where
    V: Clone + Eq + Hash,
    N: IntoIterator<Item = (V, f64)>,
    FN: FnMut(&V) -> N,
    FH: FnMut(&V) -> f64,
    FG: FnMut(&V) -> bool,
{
    let mut open_set = BinaryHeap::new();
    let mut g_score: HashMap<V, f64> = HashMap::new();
    let mut came_from: HashMap<V, V> = HashMap::new();

    let h0 = heuristic(start);
    g_score.insert(start.clone(), 0.0);
    open_set.push(State {
        f_score: h0,
        g_score: 0.0,
        vertex: start.clone(),
    });

    let mut nodes_expanded = 0usize;

    while let Some(current) = open_set.pop() {
        // 如果此状态已过时（g_score 已更新为更小值），则跳过
        if let Some(&best_g) = g_score.get(&current.vertex) {
            if current.g_score > best_g + 1e-9 {
                continue;
            }
        }

        nodes_expanded += 1;

        if is_goal(&current.vertex) {
            // 重建路径
            let mut path = vec![current.vertex.clone()];
            let mut current_vertex = current.vertex.clone();
            while let Some(prev) = came_from.get(&current_vertex) {
                path.push(prev.clone());
                current_vertex = prev.clone();
            }
            path.reverse();
            return AStarResult {
                path: Some(path),
                cost: Some(current.g_score),
                nodes_expanded,
            };
        }

        for (neighbor, edge_cost) in neighbors(&current.vertex) {
            let tentative_g = current.g_score + edge_cost;
            let existing_g = g_score.get(&neighbor).copied().unwrap_or(f64::INFINITY);

            if tentative_g < existing_g - 1e-9 {
                came_from.insert(neighbor.clone(), current.vertex.clone());
                g_score.insert(neighbor.clone(), tentative_g);
                let f = tentative_g + heuristic(&neighbor);
                open_set.push(State {
                    f_score: f,
                    g_score: tentative_g,
                    vertex: neighbor,
                });
            }
        }
    }

    AStarResult::failure(nodes_expanded)
}

/// A* 搜索的简化版本：在网格图中搜索
///
/// 假设图以 `HashMap<V, Vec<(V, f64)>>` 的邻接表形式给出。
pub fn astar_graph<V>(
    graph: &HashMap<V, Vec<(V, f64)>>,
    start: &V,
    goal: &V,
    heuristic: impl Fn(&V) -> f64,
) -> AStarResult<V>
where
    V: Clone + Eq + Hash,
{
    astar(
        start,
        |v| graph.get(v).cloned().unwrap_or_default(),
        heuristic,
        |v| v == goal,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_astar_grid() {
        let start = (0i32, 0i32);
        let goal = (2i32, 2i32);

        let result = astar(
            &start,
            |v| {
                let (x, y) = *v;
                vec![
                    ((x + 1, y), 1.0),
                    ((x - 1, y), 1.0),
                    ((x, y + 1), 1.0),
                    ((x, y - 1), 1.0),
                ]
            },
            |v| {
                let (x, y) = *v;
                ((x - goal.0).abs() + (y - goal.1).abs()) as f64
            },
            |v| *v == goal,
        );

        assert!(result.path.is_some());
        assert_eq!(result.cost, Some(4.0));
        let path = result.path.unwrap();
        assert_eq!(path.first(), Some(&start));
        assert_eq!(path.last(), Some(&goal));
    }

    #[test]
    fn test_astar_no_path() {
        let start = 0i32;
        let goal = 5i32;

        // 图: 0 -> 1 -> 2，无法到达 5
        let result = astar(
            &start,
            |v| match *v {
                0 => vec![(1, 1.0)],
                1 => vec![(2, 1.0)],
                _ => vec![],
            },
            |v| ((goal - *v).abs()) as f64,
            |v| *v == goal,
        );

        assert!(result.path.is_none());
    }

    #[test]
    fn test_astar_graph() {
        let mut graph: HashMap<char, Vec<(char, f64)>> = HashMap::new();
        graph.insert('S', vec![('A', 1.0), ('B', 4.0)]);
        graph.insert('A', vec![('B', 2.0), ('C', 5.0), ('G', 12.0)]);
        graph.insert('B', vec![('C', 1.0)]);
        graph.insert('C', vec![('G', 3.0)]);
        graph.insert('G', vec![]);

        // 启发式：到 G 的直线距离估计（简化：自定义）
        let h = |v: &char| -> f64 {
            match *v {
                'S' => 7.0,
                'A' => 6.0,
                'B' => 2.0,
                'C' => 1.0,
                'G' => 0.0,
                _ => 10.0,
            }
        };

        let result = astar_graph(&graph, &'S', &'G', h);

        assert!(result.path.is_some());
        assert_eq!(result.cost, Some(7.0)); // S -> A -> B -> C -> G = 1+2+1+3 = 7
        assert_eq!(result.path.unwrap(), vec!['S', 'A', 'B', 'C', 'G']);
    }

    #[test]
    fn test_astar_degrades_to_dijkstra() {
        // 当启发式恒为 0 时，A* 退化为 Dijkstra
        let mut graph: HashMap<char, Vec<(char, f64)>> = HashMap::new();
        graph.insert('S', vec![('A', 1.0), ('B', 4.0)]);
        graph.insert('A', vec![('B', 2.0), ('C', 5.0)]);
        graph.insert('B', vec![('C', 1.0)]);
        graph.insert('C', vec![]);

        let result = astar_graph(&graph, &'S', &'C', |_v| 0.0);

        assert!(result.path.is_some());
        // Optimal: S->A (1) + A->B (2) + B->C (1) = 4
        assert_eq!(result.cost, Some(4.0));
    }
}
