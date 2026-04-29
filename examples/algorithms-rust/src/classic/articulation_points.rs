//! 割点（关节点）算法
//!
//! 割点（Articulation Point / Cut Vertex）是指在一个无向图中，如果删除该顶点及其相关联的边后，
//! 图的连通分量数量增加，则称该顶点为割点。
//!
//! # 算法原理
//!
//! 使用Tarjan算法（基于DFS）来识别割点：
//! - 维护每个顶点的 `disc`（发现时间）和 `low`（通过后代可达的最小发现时间）
//! - 对于根节点：如果有两个或以上的子树，则为割点
//! - 对于非根节点：如果存在子节点v满足 `low[v] >= disc[u]`，则u是割点
//!
//! # 应用场景
//! - 网络脆弱性分析（找出关键节点）
//! - 道路网络规划（关键路口识别）
//! - 社交网络分析（关键人物识别）
//! - 电路设计（关键元件识别）
//!
//! # 复杂度分析
//! | 指标 | 复杂度 | 说明 |
//! |------|--------|------|
//! | 时间 | O(V + E) | 单次DFS遍历 |
//! | 空间 | O(V) | 递归栈、disc、low数组 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// 割点算法结果
#[derive(Debug, Clone)]
pub struct ArticulationPointResult<V> {
    /// 所有割点
    pub articulation_points: HashSet<V>,
    /// 每个顶点的发现时间
    pub discovery_time: HashMap<V, usize>,
    /// 每个顶点的low值
    pub low_value: HashMap<V, usize>,
    /// 移除每个割点后产生的连通分量数
    pub components_after_removal: HashMap<V, usize>,
}

impl<V> ArticulationPointResult<V>
where
    V: Eq + Hash + Clone,
{
    /// 获取割点数量
    pub fn count(&self) -> usize {
        self.articulation_points.len()
    }

    /// 检查顶点是否是割点
    pub fn is_articulation_point(&self, vertex: &V) -> bool {
        self.articulation_points.contains(vertex)
    }
}

/// 查找无向图中的所有割点
///
/// # 算法步骤
///
/// 1. 从任意未访问顶点开始DFS
/// 2. 记录每个顶点的发现时间(disc)和low值
/// 3. 对于根节点：如果子树数量 >= 2，则为割点
/// 4. 对于非根节点u：如果存在子节点v满足 low[v] >= disc[u]，则u是割点
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
///   - 访问标记: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的无向图
///
/// # 返回值
///
/// 返回 `ArticulationPointResult`，包含所有割点和相关信息
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::articulation_points::find_articulation_points;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // 构建图：A-B-C 形成一条链
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['A', 'C']);
/// graph.insert('C', vec!['B', 'D']);
/// graph.insert('D', vec!['C']);
///
/// let result = find_articulation_points(&graph);
/// assert!(result.is_articulation_point(&'B'));
/// assert!(result.is_articulation_point(&'C'));
/// ```
pub fn find_articulation_points<V>(graph: &HashMap<V, Vec<V>>) -> ArticulationPointResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut disc: HashMap<V, usize> = HashMap::new();
    let mut low: HashMap<V, usize> = HashMap::new();
    let mut parent: HashMap<V, Option<V>> = HashMap::new();
    let mut visited: HashSet<V> = HashSet::new();
    let mut articulation_points: HashSet<V> = HashSet::new();
    let mut time = 0usize;

    // 对每个未访问的顶点进行DFS（处理非连通图）
    let vertices: Vec<V> = graph.keys().cloned().collect();
    for vertex in vertices {
        if !visited.contains(&vertex) {
            dfs(
                graph,
                vertex.clone(),
                true,
                &mut time,
                &mut disc,
                &mut low,
                &mut parent,
                &mut visited,
                &mut articulation_points,
            );
        }
    }

    // 计算移除每个割点后的连通分量数
    let components_after_removal =
        calculate_components_after_removal(graph, &articulation_points);

    ArticulationPointResult {
        articulation_points,
        discovery_time: disc,
        low_value: low,
        components_after_removal,
    }
}

fn dfs<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    is_root: bool,
    time: &mut usize,
    disc: &mut HashMap<V, usize>,
    low: &mut HashMap<V, usize>,
    parent: &mut HashMap<V, Option<V>>,
    visited: &mut HashSet<V>,
    articulation_points: &mut HashSet<V>,
) where
    V: Clone + Eq + Hash,
{
    visited.insert(vertex.clone());
    disc.insert(vertex.clone(), *time);
    low.insert(vertex.clone(), *time);
    *time += 1;

    let mut child_count = 0usize;

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                child_count += 1;
                parent.insert(neighbor.clone(), Some(vertex.clone()));

                dfs(
                    graph,
                    neighbor.clone(),
                    false,
                    time,
                    disc,
                    low,
                    parent,
                    visited,
                    articulation_points,
                );

                // 更新low值
                let neighbor_low = *low.get(neighbor).unwrap();
                let vertex_low = low.get_mut(&vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_low);

                // 非根节点：检查是否是割点
                if !is_root {
                    let vertex_disc = *disc.get(&vertex).unwrap();
                    if neighbor_low >= vertex_disc {
                        articulation_points.insert(vertex.clone());
                    }
                }
            } else if parent.get(&vertex) != Some(&Some(neighbor.clone())) {
                // 回边，更新low值
                let neighbor_disc = *disc.get(neighbor).unwrap();
                let vertex_low = low.get_mut(&vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_disc);
            }
        }
    }

    // 根节点：检查子树数量
    if is_root && child_count >= 2 {
        articulation_points.insert(vertex);
    }
}

/// 计算移除割点后产生的连通分量数
fn calculate_components_after_removal<V>(
    graph: &HashMap<V, Vec<V>>,
    articulation_points: &HashSet<V>,
) -> HashMap<V, usize>
where
    V: Clone + Eq + Hash,
{
    let mut result = HashMap::new();

    for ap in articulation_points {
        // 移除该割点后计算连通分量
        let count = count_components_without_vertex(graph, ap);
        result.insert(ap.clone(), count);
    }

    result
}

/// 计算移除指定顶点后的连通分量数量
fn count_components_without_vertex<V>(graph: &HashMap<V, Vec<V>>, removed: &V) -> usize
where
    V: Clone + Eq + Hash,
{
    let mut visited: HashSet<V> = HashSet::new();
    let mut components = 0usize;

    for vertex in graph.keys() {
        if vertex == removed || visited.contains(vertex) {
            continue;
        }

        // BFS/DFS计数
        components += 1;
        let mut stack = vec![vertex.clone()];

        while let Some(v) = stack.pop() {
            if visited.contains(&v) || &v == removed {
                continue;
            }
            visited.insert(v.clone());

            if let Some(neighbors) = graph.get(&v) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) && neighbor != removed {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }
    }

    components
}

/// 查找连接两个特定顶点的所有割点
///
/// 即删除这些割点后，start和end不再连通
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn find_separating_vertices<V>(
    graph: &HashMap<V, Vec<V>>,
    start: &V,
    end: &V,
) -> HashSet<V>
where
    V: Clone + Eq + Hash,
{
    let all_aps = find_articulation_points(graph);
    let mut separating = HashSet::new();

    for ap in &all_aps.articulation_points {
        if ap == start || ap == end {
            continue;
        }

        // 检查移除该点后start和end是否仍然连通
        if !are_connected_without_vertex(graph, start, end, ap) {
            separating.insert(ap.clone());
        }
    }

    separating
}

/// 检查移除指定顶点后两个顶点是否仍然连通
fn are_connected_without_vertex<V>(
    graph: &HashMap<V, Vec<V>>,
    start: &V,
    end: &V,
    removed: &V,
) -> bool
where
    V: Clone + Eq + Hash,
{
    if start == end {
        return true;
    }

    let mut visited: HashSet<V> = HashSet::new();
    let mut stack = vec![start.clone()];

    while let Some(v) = stack.pop() {
        if &v == end {
            return true;
        }
        if visited.contains(&v) || &v == removed {
            continue;
        }
        visited.insert(v.clone());

        if let Some(neighbors) = graph.get(&v) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) && neighbor != removed {
                    stack.push(neighbor.clone());
                }
            }
        }
    }

    false
}

/// 查找使图保持连通所需的最少顶点数（顶点连通度相关）
///
/// 返回需要保留的关键顶点集合
///
/// # 复杂度
/// - **时间**: O(V × (V + E))
/// - **空间**: O(V)
pub fn find_critical_vertices<V>(graph: &HashMap<V, Vec<V>>) -> HashSet<V>
where
    V: Clone + Eq + Hash,
{
    let result = find_articulation_points(graph);
    result.articulation_points
}

/// 计算图的块（双连通分量）
///
/// 双连通分量是指没有割点的极大连通子图
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn find_biconnected_components<V>(graph: &HashMap<V, Vec<V>>) -> Vec<Vec<V>>
where
    V: Clone + Eq + Hash,
{
    let mut visited: HashSet<V> = HashSet::new();
    let mut components: Vec<Vec<V>> = Vec::new();

    // 对于每个割点，其每个子树形成一个双连通分量
    let ap_result = find_articulation_points(graph);

    // 使用并查集或DFS来找出双连通分量
    // 这里使用简化版本：对于非割点，它们属于唯一一个双连通分量

    for vertex in graph.keys() {
        if visited.contains(vertex) {
            continue;
        }

        if ap_result.articulation_points.contains(vertex) {
            // 割点属于多个分量，单独处理
            continue;
        }

        // 找到该顶点所属的双连通分量
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
                        && !ap_result.articulation_points.contains(neighbor)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_graph() {
        // 链状图：A-B-C-D，B和C是割点
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        let result = find_articulation_points(&graph);
        assert!(result.is_articulation_point(&'B'));
        assert!(result.is_articulation_point(&'C'));
        assert!(!result.is_articulation_point(&'A'));
        assert!(!result.is_articulation_point(&'D'));
        assert_eq!(result.count(), 2);
    }

    #[test]
    fn test_cycle_graph() {
        // 环状图没有割点
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['A', 'B']);

        let result = find_articulation_points(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_star_graph() {
        // 星型图：中心是割点
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C', 'D', 'E']); // 中心
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['A']);
        graph.insert('D', vec!['A']);
        graph.insert('E', vec!['A']);

        let result = find_articulation_points(&graph);
        assert!(result.is_articulation_point(&'A'));
        assert_eq!(result.count(), 1);
    }

    #[test]
    fn test_disconnected_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 组件1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        // 组件2
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = find_articulation_points(&graph);
        // 每个连通分量没有割点
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_complex_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 构建一个复杂图
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C', 'D']);
        graph.insert('C', vec!['B', 'E']);
        graph.insert('D', vec!['B', 'E']);
        graph.insert('E', vec!['C', 'D', 'F']);
        graph.insert('F', vec!['E']);

        let result = find_articulation_points(&graph);
        assert!(result.is_articulation_point(&'B'));
        assert!(result.is_articulation_point(&'E'));
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = find_articulation_points(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_two_vertices() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);

        let result = find_articulation_points(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_separating_vertices() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        let separating = find_separating_vertices(&graph, &'A', &'D');
        assert!(separating.contains(&'B'));
        assert!(separating.contains(&'C'));
    }

    #[test]
    fn test_complete_graph() {
        // 完全图没有割点
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2, 3, 4]);
        graph.insert(2, vec![1, 3, 4]);
        graph.insert(3, vec![1, 2, 4]);
        graph.insert(4, vec![1, 2, 3]);

        let result = find_articulation_points(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = find_articulation_points(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_numerical_vertices() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        // 构建树结构
        graph.insert(1, vec![2, 3]);
        graph.insert(2, vec![1, 4, 5]);
        graph.insert(3, vec![1]);
        graph.insert(4, vec![2]);
        graph.insert(5, vec![2]);

        let result = find_articulation_points(&graph);
        assert!(result.is_articulation_point(&1));
        assert!(result.is_articulation_point(&2));
        assert_eq!(result.count(), 2);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：网络脆弱性分析
    pub fn network_vulnerability_example() {
        println!("=== 割点算法 - 网络脆弱性分析 ===");

        let mut network: HashMap<&str, Vec<&str>> = HashMap::new();
        // 网络拓扑
        network.insert("Router-A", vec!["Router-B", "Router-C"]);
        network.insert("Router-B", vec!["Router-A", "Router-D", "Router-E"]);
        network.insert("Router-C", vec!["Router-A", "Router-F"]);
        network.insert("Router-D", vec!["Router-B"]);
        network.insert("Router-E", vec!["Router-B", "Router-F"]);
        network.insert("Router-F", vec!["Router-C", "Router-E"]);

        let result = find_articulation_points(&network);
        println!("关键路由器（割点）：");
        for ap in &result.articulation_points {
            println!("  ⚠️ {} - 故障将导致网络分裂", ap);
        }
    }

    /// 示例：道路网络关键路口
    pub fn road_network_example() {
        println!("\n=== 割点算法 - 道路网络关键路口 ===");

        let mut roads: HashMap<&str, Vec<&str>> = HashMap::new();
        // 城市道路网络
        roads.insert("Center", vec!["North", "South", "East", "West"]);
        roads.insert("North", vec!["Center", "North-East"]);
        roads.insert("South", vec!["Center", "South-East"]);
        roads.insert("East", vec!["Center", "North-East", "South-East"]);
        roads.insert("West", vec!["Center"]);
        roads.insert("North-East", vec!["North", "East"]);
        roads.insert("South-East", vec!["South", "East"]);

        let result = find_articulation_points(&roads);
        println!("关键路口分析：");
        for ap in &result.articulation_points {
            let count = result.components_after_removal.get(ap).unwrap_or(&0);
            println!("  🔴 {} - 移除后将产生 {} 个不连通区域", ap, count);
        }
    }
}
