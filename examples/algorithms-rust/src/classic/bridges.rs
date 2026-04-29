//! 桥（Bridge / Cut Edge）算法
//!
//! 桥是指在一个无向图中，如果删除该边后，图的连通分量数量增加，
//! 则称该边为桥（或割边）。桥是图中的关键连接。
//!
//! # 算法原理
//!
//! 使用Tarjan算法（基于DFS）来识别桥：
//! - 维护每个顶点的 `disc`（发现时间）和 `low`（通过后代可达的最小发现时间）
//! - 对于边(u, v)，如果 `low[v] > disc[u]`，则(u, v)是桥
//!
//! 条件 `low[v] > disc[u]` 意味着v及其后代无法通过回边到达u或其祖先，
//! 因此(u, v)是连接两个部分的唯一路径。
//!
//! # 应用场景
//! - 网络基础设施设计（关键链路识别）
//! - 道路网络规划（关键桥梁/隧道）
//! - 电力网络分析（关键输电线路）
//! - 社交网络分析（关键关系识别）
//!
//! # 复杂度分析
//! | 指标 | 复杂度 | 说明 |
//! |------|--------|------|
//! | 时间 | O(V + E) | 单次DFS遍历 |
//! | 空间 | O(V) | 递归栈、disc、low数组 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// 边类型（无向边）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Edge<V> {
    /// 边的第一个端点
    pub u: V,
    /// 边的第二个端点
    pub v: V,
}

impl<V: Clone + Ord> Edge<V> {
    /// 创建规范化边（较小的顶点在前）
    pub fn new(u: V, v: V) -> Self {
        if u < v {
            Edge { u, v }
        } else {
            Edge { u: v, v: u }
        }
    }
}

/// 桥算法结果
#[derive(Debug, Clone)]
pub struct BridgeResult<V> {
    /// 所有桥边
    pub bridges: HashSet<Edge<V>>,
    /// 每个顶点的发现时间
    pub discovery_time: HashMap<V, usize>,
    /// 每个顶点的low值
    pub low_value: HashMap<V, usize>,
    /// 移除所有桥后的连通分量
    pub bridge_tree_components: Vec<Vec<V>>,
}

impl<V> BridgeResult<V>
where
    V: Clone + Ord + Hash + Eq,
{
    /// 获取桥的数量
    pub fn count(&self) -> usize {
        self.bridges.len()
    }

    /// 检查边是否是桥
    pub fn is_bridge(&self, u: V, v: V) -> bool {
        self.bridges.contains(&Edge::new(u, v))
    }

    /// 获取桥边列表
    pub fn get_bridges_vec(&self) -> Vec<&Edge<V>> {
        self.bridges.iter().collect()
    }
}

/// 查找无向图中的所有桥
///
/// # 算法步骤
///
/// 1. 从任意未访问顶点开始DFS
/// 2. 记录每个顶点的发现时间(disc)和low值
/// 3. 对于边(u, v)，如果 `low[v] > disc[u]`，则(u, v)是桥
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 每个顶点访问一次
///   - 每条边检查两次（无向图）
///
/// - **空间复杂度**: O(V)
///   - 递归调用栈: O(V)
///   - disc和low数组: O(V)
///   - 父节点记录: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的无向图
///
/// # 返回值
///
/// 返回 `BridgeResult`，包含所有桥边和相关信息
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::bridges::find_bridges;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // 构建图：A-B-C，其中B-C是桥
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['A', 'C']);
/// graph.insert('C', vec!['B', 'D', 'E']);
/// graph.insert('D', vec!['C', 'E']);
/// graph.insert('E', vec!['C', 'D']);
///
/// let result = find_bridges(&graph);
/// assert!(result.is_bridge('B', 'C'));
/// assert!(!result.is_bridge('C', 'D'));
/// ```
pub fn find_bridges<V>(graph: &HashMap<V, Vec<V>>) -> BridgeResult<V>
where
    V: Clone + Ord + Hash + Eq,
{
    let mut disc: HashMap<V, usize> = HashMap::new();
    let mut low: HashMap<V, usize> = HashMap::new();
    let mut parent: HashMap<V, Option<V>> = HashMap::new();
    let mut visited: HashSet<V> = HashSet::new();
    let mut bridges: HashSet<Edge<V>> = HashSet::new();
    let mut time = 0usize;

    // 对每个未访问的顶点进行DFS
    let vertices: Vec<V> = graph.keys().cloned().collect();
    for vertex in vertices {
        if !visited.contains(&vertex) {
            dfs(
                graph,
                vertex.clone(),
                &mut time,
                &mut disc,
                &mut low,
                &mut parent,
                &mut visited,
                &mut bridges,
            );
        }
    }

    // 计算桥树连通分量（移除所有桥后的连通分量）
    let bridge_tree_components = find_bridge_tree_components(graph, &bridges);

    BridgeResult {
        bridges,
        discovery_time: disc,
        low_value: low,
        bridge_tree_components,
    }
}

fn dfs<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    time: &mut usize,
    disc: &mut HashMap<V, usize>,
    low: &mut HashMap<V, usize>,
    parent: &mut HashMap<V, Option<V>>,
    visited: &mut HashSet<V>,
    bridges: &mut HashSet<Edge<V>>,
) where
    V: Clone + Ord + Hash + Eq,
{
    visited.insert(vertex.clone());
    disc.insert(vertex.clone(), *time);
    low.insert(vertex.clone(), *time);
    *time += 1;

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                parent.insert(neighbor.clone(), Some(vertex.clone()));

                dfs(
                    graph,
                    neighbor.clone(),
                    time,
                    disc,
                    low,
                    parent,
                    visited,
                    bridges,
                );

                // 更新low值
                let neighbor_low = *low.get(neighbor).unwrap();
                let vertex_low = low.get_mut(&vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_low);

                // 检查是否是桥
                let vertex_disc = *disc.get(&vertex).unwrap();
                if neighbor_low > vertex_disc {
                    bridges.insert(Edge::new(vertex.clone(), neighbor.clone()));
                }
            } else if parent.get(&vertex) != Some(&Some(neighbor.clone())) {
                // 回边，更新low值
                let neighbor_disc = *disc.get(neighbor).unwrap();
                let vertex_low = low.get_mut(&vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_disc);
            }
        }
    }
}

/// 查找移除所有桥后的连通分量（桥树中的节点）
fn find_bridge_tree_components<V>(
    graph: &HashMap<V, Vec<V>>,
    bridges: &HashSet<Edge<V>>,
) -> Vec<Vec<V>>
where
    V: Clone + Ord + Hash + Eq,
{
    let mut visited: HashSet<V> = HashSet::new();
    let mut components: Vec<Vec<V>> = Vec::new();

    for vertex in graph.keys() {
        if visited.contains(vertex) {
            continue;
        }

        let mut component = Vec::new();
        let mut stack = vec![vertex.clone()];

        while let Some(v) = stack.pop() {
            if visited.contains(&v) {
                continue;
            }
            visited.insert(v.clone());
            component.push(v.clone());

            if let Some(neighbors) = graph.get(&v) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor)
                        && !bridges.contains(&Edge::new(v.clone(), neighbor.clone()))
                    {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }

        if !component.is_empty() {
            components.push(component);
        }
    }

    components
}

/// 构建桥树（将每个双连通分量收缩为一个节点）
///
/// 桥树是一棵树，其中每条边对应原图中的一座桥
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn build_bridge_tree<V>(
    graph: &HashMap<V, Vec<V>>,
    bridges: &HashSet<Edge<V>>,
) -> HashMap<usize, Vec<usize>>
where
    V: Clone + Ord + Hash + Eq,
{
    // 找到所有双连通分量
    let components = find_bridge_tree_components(graph, bridges);

    // 建立顶点到分量编号的映射
    let mut vertex_to_component: HashMap<V, usize> = HashMap::new();
    for (i, comp) in components.iter().enumerate() {
        for v in comp {
            vertex_to_component.insert(v.clone(), i);
        }
    }

    // 构建桥树
    let mut tree: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..components.len() {
        tree.insert(i, Vec::new());
    }

    for bridge in bridges {
        let u_comp = vertex_to_component.get(&bridge.u).copied().unwrap();
        let v_comp = vertex_to_component.get(&bridge.v).copied().unwrap();
        tree.entry(u_comp).or_default().push(v_comp);
        tree.entry(v_comp).or_default().push(u_comp);
    }

    tree
}

/// 检查移除某条边后图是否仍然连通
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn is_critical_edge<V>(graph: &HashMap<V, Vec<V>>, u: &V, v: &V) -> bool
where
    V: Clone + Ord + Hash + Eq,
{
    let result = find_bridges(graph);
    result.is_bridge(u.clone(), v.clone())
}

/// 查找连接两个顶点的所有关键边
///
/// 移除这些边后，两个顶点不再连通
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn find_critical_edges<V>(graph: &HashMap<V, Vec<V>>, start: &V, end: &V) -> Vec<Edge<V>>
where
    V: Clone + Ord + Hash + Eq,
{
    let result = find_bridges(graph);
    let mut critical = Vec::new();

    for bridge in &result.bridges {
        // 检查移除该桥后start和end是否仍然连通
        if !are_connected_without_edge(graph, start, end, &bridge.u, &bridge.v) {
            critical.push(bridge.clone());
        }
    }

    critical
}

/// 检查移除指定边后两个顶点是否仍然连通
fn are_connected_without_edge<V>(
    graph: &HashMap<V, Vec<V>>,
    start: &V,
    end: &V,
    u: &V,
    v: &V,
) -> bool
where
    V: Clone + Ord + Hash + Eq,
{
    if start == end {
        return true;
    }

    let mut visited: HashSet<V> = HashSet::new();
    let mut stack = vec![start.clone()];

    while let Some(vertex) = stack.pop() {
        if &vertex == end {
            return true;
        }
        if visited.contains(&vertex) {
            continue;
        }
        visited.insert(vertex.clone());

        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                if visited.contains(neighbor) {
                    continue;
                }
                // 跳过被移除的边
                if (&vertex == u && neighbor == v) || (&vertex == v && neighbor == u) {
                    continue;
                }
                stack.push(neighbor.clone());
            }
        }
    }

    false
}

/// 计算图的边连通度
///
/// 边连通度是指使图不连通需要删除的最少边数
///
/// # 复杂度
/// - **时间**: O(V × (V + E)) 使用更简单的方法
/// - **空间**: O(V + E)
pub fn edge_connectivity<V>(graph: &HashMap<V, Vec<V>>) -> usize
where
    V: Clone + Ord + Hash + Eq,
{
    if graph.is_empty() {
        return 0;
    }

    // 找到桥的数量
    let result = find_bridges(graph);

    // 如果没有桥，图是2-边连通的
    if result.count() == 0 {
        return 2; // 至少是2，实际可能更大
    }

    // 如果有桥，边连通度为1
    1
}

/// 找到使图成为2-边连通图需要添加的最少边数
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn min_edges_to_make_2_edge_connected<V>(graph: &HashMap<V, Vec<V>>) -> usize
where
    V: Clone + Ord + Hash + Eq,
{
    let result = find_bridges(graph);

    if result.count() == 0 {
        return 0; // 已经是2-边连通
    }

    // 构建桥树，计算叶子节点数量
    let bridge_tree = build_bridge_tree(graph, &result.bridges);

    if bridge_tree.len() <= 1 {
        return 0;
    }

    // 统计桥树的叶子节点
    let leaves = bridge_tree
        .iter()
        .filter(|(_, neighbors)| neighbors.len() == 1)
        .count();

    // 需要添加的边数 = (叶子数 + 1) / 2
    (leaves + 1) / 2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_graph() {
        // 链状图中所有边都是桥
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 3);
        assert!(result.is_bridge('A', 'B'));
        assert!(result.is_bridge('B', 'C'));
        assert!(result.is_bridge('C', 'D'));
    }

    #[test]
    fn test_cycle_graph() {
        // 环状图没有桥
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['A', 'B']);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_two_cycles_connected() {
        // 两个环通过一条边连接，这条边是桥
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 第一个环 A-B-C-A
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A', 'C', 'D']);
        graph.insert('C', vec!['A', 'B']);
        // 桥 D-E
        graph.insert('D', vec!['B', 'E']);
        graph.insert('E', vec!['D', 'F']);
        // 第二个环 E-F-G-E
        graph.insert('F', vec!['E', 'G']);
        graph.insert('G', vec!['F', 'E']);

        let result = find_bridges(&graph);
        // D-E 和 B-D 都可能是桥
        assert!(result.count() >= 1);
        assert!(result.is_bridge('D', 'E'));
    }

    #[test]
    fn test_star_graph() {
        // 星型图中所有边都是桥
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C', 'D', 'E']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['A']);
        graph.insert('D', vec!['A']);
        graph.insert('E', vec!['A']);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 4);
    }

    #[test]
    fn test_complete_graph() {
        // 完全图没有桥
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2, 3, 4]);
        graph.insert(2, vec![1, 3, 4]);
        graph.insert(3, vec![1, 2, 4]);
        graph.insert(4, vec![1, 2, 3]);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_bridge_tree() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        let result = find_bridges(&graph);
        let tree = build_bridge_tree(&graph, &result.bridges);

        // 桥树应该有4个节点（每条边都是一个桥）
        assert_eq!(tree.len(), 4);
    }

    #[test]
    fn test_edge_connectivity() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B']);

        // 有一条桥，边连通度为1
        assert_eq!(edge_connectivity(&graph), 1);

        let mut cycle: HashMap<char, Vec<char>> = HashMap::new();
        cycle.insert('A', vec!['B', 'C']);
        cycle.insert('B', vec!['A', 'C']);
        cycle.insert('C', vec!['A', 'B']);

        // 没有桥，至少是2-边连通
        assert_eq!(edge_connectivity(&cycle), 2);
    }

    #[test]
    fn test_critical_edges() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        let critical = find_critical_edges(&graph, &'A', &'D');
        assert_eq!(critical.len(), 3); // 所有边都是关键边
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = find_bridges(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_two_vertices() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 1); // 唯一的边是桥
    }

    #[test]
    fn test_disconnected_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = find_bridges(&graph);
        assert_eq!(result.count(), 2); // 每条边都是桥
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：网络基础设施关键链路
    pub fn network_critical_links_example() {
        println!("=== 桥算法 - 网络关键链路分析 ===");

        let mut network: HashMap<&str, Vec<&str>> = HashMap::new();
        // 数据中心网络拓扑
        network.insert("DC-Core", vec!["Router-A", "Router-B"]);
        network.insert("Router-A", vec!["DC-Core", "Switch-1", "Switch-2"]);
        network.insert("Router-B", vec!["DC-Core", "Switch-3"]);
        network.insert("Switch-1", vec!["Router-A", "Server-1", "Server-2"]);
        network.insert("Switch-2", vec!["Router-A", "Server-3"]);
        network.insert("Switch-3", vec!["Router-B", "Server-4"]);
        network.insert("Server-1", vec!["Switch-1", "Server-2"]);
        network.insert("Server-2", vec!["Switch-1", "Server-1"]);
        network.insert("Server-3", vec!["Switch-2"]);
        network.insert("Server-4", vec!["Switch-3"]);

        let result = find_bridges(&network);
        println!("关键网络链路（桥）：");
        for bridge in &result.bridges {
            println!("  ⚠️ {} <-> {} - 故障将导致网络分裂", bridge.u, bridge.v);
        }

        println!("\n网络冗余度分析：");
        if result.count() == 0 {
            println!("  ✓ 网络完全冗余，无单点故障");
        } else {
            println!("  ✗ 存在 {} 处单点故障风险", result.count());
        }
    }

    /// 示例：道路网络关键桥梁
    pub fn road_network_bridges_example() {
        println!("\n=== 桥算法 - 道路关键桥梁/隧道分析 ===");

        let mut roads: HashMap<&str, Vec<&str>> = HashMap::new();
        // 城市道路网络，包含一座关键桥梁
        roads.insert("City-A", vec!["Bridge-1", "Highway-1"]);
        roads.insert("Bridge-1", vec!["City-A", "City-B"]);
        roads.insert("City-B", vec!["Bridge-1", "Ring-Road-1"]);
        roads.insert("Ring-Road-1", vec!["City-B", "District-1", "District-2"]);
        roads.insert("District-1", vec!["Ring-Road-1", "District-2"]);
        roads.insert("District-2", vec!["Ring-Road-1", "District-1"]);
        roads.insert("Highway-1", vec!["City-A", "City-C"]);
        roads.insert("City-C", vec!["Highway-1"]);

        let result = find_bridges(&roads);
        println!("交通关键节点：");
        for bridge in &result.bridges {
            println!("  🔴 {} <-> {} - 关键连接", bridge.u, bridge.v);
        }

        let min_edges = min_edges_to_make_2_edge_connected(&roads);
        if min_edges > 0 {
            println!("\n建议：需要添加 {} 条冗余道路以提高可靠性", min_edges);
        }
    }
}
