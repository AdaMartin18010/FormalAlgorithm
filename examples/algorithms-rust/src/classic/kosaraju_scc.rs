//! Kosaraju强连通分量算法
//!
//! Kosaraju算法是一种用于查找有向图中强连通分量(SCC)的经典算法。
//! 它通过两次深度优先搜索(DFS)来识别所有强连通分量。
//!
//! # 算法原理
//!
//! Kosaraju算法基于以下关键观察：
//! 1. 对原图G进行DFS，按完成时间逆序排列顶点
//! 2. 计算原图的转置图G^T（所有边反向）
//! 3. 按完成时间逆序对G^T进行DFS，每次DFS访问的顶点构成一个SCC
//!
//! # 为什么有效？
//!
//! 在转置图上按照原图DFS完成时间的逆序进行遍历，确保我们总是从"最深处"的SCC开始，
//! 这样不会访问到其他SCC中的顶点（原图中只有从编号小的SCC指向编号大的SCC的边）。
//!
//! # 应用场景
//! - 网页链接分析（PageRank预处理）
//! - 社交网络社区检测
//! - 编译器优化（控制流分析）
//! - 电路设计分析
//!
//! # 复杂度分析
//! | 指标 | 复杂度 | 说明 |
//! |------|--------|------|
//! | 时间 | O(V + E) | 两次DFS遍历，每次O(V+E) |
//! | 空间 | O(V + E) | 转置图需要O(V+E)空间 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Kosaraju SCC结果
#[derive(Debug, Clone)]
pub struct KosarajuSCCResult<V> {
    /// 所有强连通分量
    pub components: Vec<Vec<V>>,
    /// 每个顶点所属的分量编号
    pub vertex_to_component: HashMap<V, usize>,
    /// 缩点后的DAG
    pub condensed_graph: HashMap<usize, HashSet<usize>>,
}

impl<V> KosarajuSCCResult<V>
where
    V: Eq + Hash + Clone,
{
    /// 获取强连通分量数量
    pub fn count(&self) -> usize {
        self.components.len()
    }

    /// 检查两个顶点是否在同一个SCC中
    pub fn in_same_scc(&self, v1: &V, v2: &V) -> bool {
        self.vertex_to_component
            .get(v1)
            .and_then(|c1| self.vertex_to_component.get(v2).map(|c2| c1 == c2))
            .unwrap_or(false)
    }

    /// 获取指定顶点所在的SCC
    pub fn get_scc(&self, vertex: &V) -> Option<&Vec<V>> {
        self.vertex_to_component
            .get(vertex)
            .and_then(|&id| self.components.get(id))
    }
}

/// Kosaraju强连通分量算法
///
/// # 算法步骤
///
/// 1. **第一次DFS**: 在原图上进行DFS，记录顶点的完成顺序
/// 2. **构建转置图**: 将所有边的方向反转
/// 3. **第二次DFS**: 按照完成顺序的逆序，在转置图上进行DFS，每次访问的顶点构成一个SCC
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 第一次DFS: O(V + E)
///   - 构建转置图: O(V + E)
///   - 第二次DFS: O(V + E)
///
/// - **空间复杂度**: O(V + E)
///   - 访问标记数组: O(V)
///   - 递归栈: O(V)
///   - 转置图存储: O(V + E)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图
///
/// # 返回值
///
/// 返回 `KosarajuSCCResult`，包含所有强连通分量
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::kosaraju_scc::kosaraju_scc;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // SCC 1: A-B-C 循环
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['C']);
/// graph.insert('C', vec!['A', 'D']);
/// // SCC 2: D-E 循环
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec!['D']);
///
/// let result = kosaraju_scc(&graph);
/// assert_eq!(result.count(), 2);
/// assert!(result.in_same_scc(&'A', &'C'));
/// assert!(!result.in_same_scc(&'A', &'D'));
/// ```
pub fn kosaraju_scc<V>(graph: &HashMap<V, Vec<V>>) -> KosarajuSCCResult<V>
where
    V: Clone + Eq + Hash,
{
    // 收集所有顶点
    let all_vertices: Vec<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();

    // 第一次DFS：获取完成顺序
    let mut visited: HashSet<V> = HashSet::new();
    let mut finish_order: Vec<V> = Vec::new();

    for vertex in &all_vertices {
        if !visited.contains(vertex) {
            dfs_first_pass(graph, vertex.clone(), &mut visited, &mut finish_order);
        }
    }

    // 构建转置图
    let transpose = build_transpose(graph);

    // 第二次DFS：按完成顺序逆序遍历转置图
    visited.clear();
    let mut components: Vec<Vec<V>> = Vec::new();
    let mut vertex_to_component: HashMap<V, usize> = HashMap::new();

    for vertex in finish_order.into_iter().rev() {
        if !visited.contains(&vertex) {
            let mut component = Vec::new();
            dfs_second_pass(&transpose, vertex, &mut visited, &mut component);

            let component_id = components.len();
            for v in &component {
                vertex_to_component.insert(v.clone(), component_id);
            }
            components.push(component);
        }
    }

    // 构建缩点图
    let condensed_graph = build_condensed_graph(graph, &vertex_to_component, components.len());

    KosarajuSCCResult {
        components,
        vertex_to_component,
        condensed_graph,
    }
}

/// 第一次DFS：获取顶点完成顺序
fn dfs_first_pass<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    visited: &mut HashSet<V>,
    finish_order: &mut Vec<V>,
) where
    V: Clone + Eq + Hash,
{
    visited.insert(vertex.clone());

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                dfs_first_pass(graph, neighbor.clone(), visited, finish_order);
            }
        }
    }

    finish_order.push(vertex);
}

/// 第二次DFS：在转置图上收集SCC
fn dfs_second_pass<V>(
    transpose: &HashMap<V, Vec<V>>,
    vertex: V,
    visited: &mut HashSet<V>,
    component: &mut Vec<V>,
) where
    V: Clone + Eq + Hash,
{
    visited.insert(vertex.clone());
    component.push(vertex.clone());

    if let Some(neighbors) = transpose.get(&vertex) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                dfs_second_pass(transpose, neighbor.clone(), visited, component);
            }
        }
    }
}

/// 构建转置图（边方向反转）
fn build_transpose<V>(graph: &HashMap<V, Vec<V>>) -> HashMap<V, Vec<V>>
where
    V: Clone + Eq + Hash,
{
    let mut transpose: HashMap<V, Vec<V>> = HashMap::new();

    // 初始化所有顶点
    for vertex in graph.keys() {
        transpose.entry(vertex.clone()).or_default();
    }

    // 添加反向边
    for (vertex, neighbors) in graph.iter() {
        for neighbor in neighbors {
            transpose
                .entry(neighbor.clone())
                .or_default()
                .push(vertex.clone());
        }
    }

    transpose
}

/// 构建缩点后的DAG
fn build_condensed_graph<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex_to_component: &HashMap<V, usize>,
    num_components: usize,
) -> HashMap<usize, HashSet<usize>>
where
    V: Clone + Eq + Hash,
{
    let mut condensed: HashMap<usize, HashSet<usize>> = HashMap::new();

    for i in 0..num_components {
        condensed.insert(i, HashSet::new());
    }

    for (vertex, neighbors) in graph.iter() {
        if let Some(&from) = vertex_to_component.get(vertex) {
            for neighbor in neighbors {
                if let Some(&to) = vertex_to_component.get(neighbor) {
                    if from != to {
                        condensed.entry(from).or_default().insert(to);
                    }
                }
            }
        }
    }

    condensed
}

/// 检查图是否强连通
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn is_strongly_connected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    let result = kosaraju_scc(graph);
    result.count() == 1
}

/// 获取SCC的拓扑排序（按Kosaraju算法发现的顺序）
///
/// 返回的分量编号数组已经按照拓扑序排列（源点到汇点）
pub fn scc_topological_order<V>(result: &KosarajuSCCResult<V>) -> Vec<usize>
where
    V: Clone + Eq + Hash,
{
    (0..result.count()).collect()
}

/// 统计每个SCC的大小
pub fn scc_size_distribution<V>(result: &KosarajuSCCResult<V>) -> Vec<usize>
where
    V: Clone + Eq + Hash,
{
    result.components.iter().map(|c| c.len()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_cycle() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 1);
        assert_eq!(result.components[0].len(), 3);
    }

    #[test]
    fn test_two_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A', 'D']);
        // SCC 2
        graph.insert('D', vec!['E']);
        graph.insert('E', vec!['D']);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 2);
        assert!(result.in_same_scc(&'A', &'B'));
        assert!(result.in_same_scc(&'D', &'E'));
        assert!(!result.in_same_scc(&'A', &'D'));
    }

    #[test]
    fn test_dag_each_vertex_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['D']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec![]);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 4); // 每个顶点是一个SCC
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 1);
        assert!(result.components[0].contains(&'A'));
    }

    #[test]
    fn test_self_loop() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['A']);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 1);
        assert!(is_strongly_connected(&graph));
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_complex_graph() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        // SCC 1: 1-2-3
        graph.insert(1, vec![2]);
        graph.insert(2, vec![3, 4]);
        graph.insert(3, vec![1]);
        // SCC 2: 4-5-6
        graph.insert(4, vec![5]);
        graph.insert(5, vec![6]);
        graph.insert(6, vec![4, 7]);
        // SCC 3: 7
        graph.insert(7, vec![]);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 3);
    }

    #[test]
    fn test_disconnected_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        // SCC 2 (disconnected)
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 2);
    }

    #[test]
    fn test_is_strongly_connected() {
        let mut scc: HashMap<char, Vec<char>> = HashMap::new();
        scc.insert('A', vec!['B']);
        scc.insert('B', vec!['C']);
        scc.insert('C', vec!['A']);
        assert!(is_strongly_connected(&scc));

        let mut non_scc: HashMap<char, Vec<char>> = HashMap::new();
        non_scc.insert('A', vec!['B']);
        non_scc.insert('B', vec![]);
        assert!(!is_strongly_connected(&non_scc));
    }

    #[test]
    fn test_condensed_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 线性链: A -> B -> C
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec![]);

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 3);

        // 检查缩点图有正确的边
        let sizes: Vec<usize> = result.components.iter().map(|c| c.len()).collect();
        assert!(sizes.iter().all(|&s| s == 1)); // 每个SCC大小为1
    }

    #[test]
    fn test_size_distribution() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC大小为3
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);
        // SCC大小为1
        graph.insert('D', vec![]);

        let result = kosaraju_scc(&graph);
        let sizes = scc_size_distribution(&result);
        assert!(sizes.contains(&3));
        assert!(sizes.contains(&1));
    }

    #[test]
    fn test_large_graph() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        // 创建100个顶点，每10个形成一个环
        for i in 0..100 {
            let next = if (i + 1) % 10 == 0 { i - 9 } else { i + 1 };
            graph.insert(i, vec![next]);
        }

        let result = kosaraju_scc(&graph);
        assert_eq!(result.count(), 10); // 10个SCC，每个大小为10
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：网页链接分析
    pub fn web_link_analysis_example() {
        println!("=== Kosaraju算法 - 网页链接分析 ===");

        let mut web_graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // 强连通组件1：互相引用的页面
        web_graph.insert("首页", vec!["产品页", "关于我们"]);
        web_graph.insert("产品页", vec!["首页", "定价页"]);
        web_graph.insert("定价页", vec!["产品页", "首页"]);
        // 强连通组件2：博客系统
        web_graph.insert("博客首页", vec!["文章1", "文章2"]);
        web_graph.insert("文章1", vec!["博客首页", "文章2"]);
        web_graph.insert("文章2", vec!["博客首页", "文章1"]);
        // 联系我们（汇点）
        web_graph.insert("关于我们", vec!["联系我们"]);
        web_graph.insert("联系我们", vec![]);

        let result = kosaraju_scc(&web_graph);
        println!("网页结构分析：");
        for (i, scc) in result.components.iter().enumerate() {
            println!("  组件 {}: {:?}", i + 1, scc);
        }

        println!("\n缩点图结构：");
        for (from, to_set) in &result.condensed_graph {
            if !to_set.is_empty() {
                println!("  组件 {} -> {:?}", from + 1, 
                    to_set.iter().map(|x| x + 1).collect::<Vec<_>>());
            }
        }
    }

    /// 示例：软件包依赖分析
    pub fn package_dependency_example() {
        println!("\n=== Kosaraju算法 - 软件包依赖分析 ===");

        let mut deps: HashMap<&str, Vec<&str>> = HashMap::new();
        // 循环依赖组（需要解决）
        deps.insert("pkg-a", vec!["pkg-b"]);
        deps.insert("pkg-b", vec!["pkg-c"]);
        deps.insert("pkg-c", vec!["pkg-a", "pkg-utils"]);
        // 工具包循环依赖
        deps.insert("pkg-utils", vec!["pkg-helpers"]);
        deps.insert("pkg-helpers", vec!["pkg-utils"]);

        let result = kosaraju_scc(&deps);
        println!("软件包分析结果：");
        for (i, scc) in result.components.iter().enumerate() {
            if scc.len() > 1 {
                println!("  ⚠️  循环依赖组 {}: {:?}", i + 1, scc);
            } else {
                println!("     独立包 {}: {:?}", i + 1, scc);
            }
        }
    }
}
