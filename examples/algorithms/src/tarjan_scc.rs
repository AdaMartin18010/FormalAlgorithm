//! Tarjan强连通分量算法
//!
//! Tarjan算法是一种用于查找有向图中强连通分量(SCC)的线性时间算法。
//! 它基于深度优先搜索(DFS)，通过维护每个顶点的索引(index)和low-link值来识别SCC。
//!
//! # 算法原理
//!
//! - **index**: 顶点在DFS遍历中的访问顺序
//! - **low-link**: 从该顶点出发通过零条或多条树边和至多一条后向边/横叉边可达的最小index
//!
//! 当 `index == low-link` 时，当前顶点是SCC的根节点，栈中该顶点之上的所有顶点构成一个SCC。
//!
//! # 应用场景
//! - 社交网络中的社区发现
//! - 编译器控制流分析
//! - 2-SAT问题求解
//! - 网页链接分析
//!
//! # 复杂度分析
//! | 指标 | 复杂度 | 说明 |
//! |------|--------|------|
//! | 时间 | O(V + E) | 每个顶点访问一次，每条边检查一次 |
//! | 空间 | O(V) | 递归栈、显式栈、index/lowlink数组 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Tarjan SCC结果
#[derive(Debug, Clone)]
pub struct TarjanSCCResult<V> {
    /// 所有强连通分量
    pub components: Vec<Vec<V>>,
    /// 每个顶点所属的分量编号
    pub vertex_to_component: HashMap<V, usize>,
    /// 缩点后的DAG（分量图）
    pub condensed_graph: HashMap<usize, HashSet<usize>>,
}

impl<V> TarjanSCCResult<V>
where
    V: Eq + Hash + Clone,
{
    /// 获取强连通分量的数量
    pub fn count(&self) -> usize {
        self.components.len()
    }

    /// 检查两个顶点是否在同一个强连通分量中
    pub fn same_component(&self, v1: &V, v2: &V) -> bool {
        self.vertex_to_component
            .get(v1)
            .and_then(|c1| self.vertex_to_component.get(v2).map(|c2| c1 == c2))
            .unwrap_or(false)
    }

    /// 获取指定顶点所在的分量
    pub fn get_component(&self, vertex: &V) -> Option<&Vec<V>> {
        self.vertex_to_component
            .get(vertex)
            .and_then(|&id| self.components.get(id))
    }
}

/// Tarjan强连通分量算法
///
/// # 算法步骤
///
/// 1. 对未访问的顶点开始DFS
/// 2. 为顶点分配index和lowlink值
/// 3. 将顶点压入栈
/// 4. 递归访问邻居，更新lowlink值
/// 5. 若index == lowlink，弹出栈顶元素直到当前顶点，构成一个SCC
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 每个顶点恰好访问一次
///   - 每条边恰好检查一次
///
/// - **空间复杂度**: O(V)
///   - 递归调用栈: O(V)
///   - 显式栈存储顶点: O(V)
///   - index和lowlink数组: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图，顶点需实现Clone + Eq + Hash
///
/// # 返回值
///
/// 返回 `TarjanSCCResult`，包含所有强连通分量及其相关信息
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::tarjan_scc::tarjan_scc;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // SCC 1: A <-> B <-> C
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['C']);
/// graph.insert('C', vec!['A', 'D']);
/// // SCC 2: D <-> E
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec!['D']);
///
/// let result = tarjan_scc(&graph);
/// assert_eq!(result.count(), 2);
/// assert!(result.same_component(&'A', &'B'));
/// assert!(!result.same_component(&'A', &'D'));
/// ```
pub fn tarjan_scc<V>(graph: &HashMap<V, Vec<V>>) -> TarjanSCCResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut index = 0usize;
    let mut indices: HashMap<V, usize> = HashMap::new();
    let mut lowlinks: HashMap<V, usize> = HashMap::new();
    let mut stack: Vec<V> = Vec::new();
    let mut on_stack: HashSet<V> = HashSet::new();
    let mut components: Vec<Vec<V>> = Vec::new();
    let mut vertex_to_component: HashMap<V, usize> = HashMap::new();

    // 收集所有顶点
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    for vertex in all_vertices {
        if !indices.contains_key(&vertex) {
            strong_connect(
                graph,
                &vertex,
                &mut index,
                &mut indices,
                &mut lowlinks,
                &mut stack,
                &mut on_stack,
                &mut components,
                &mut vertex_to_component,
            );
        }
    }

    // 构建缩点后的DAG
    let condensed_graph = build_condensed_graph(graph, &vertex_to_component, components.len());

    TarjanSCCResult {
        components,
        vertex_to_component,
        condensed_graph,
    }
}

fn strong_connect<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: &V,
    index: &mut usize,
    indices: &mut HashMap<V, usize>,
    lowlinks: &mut HashMap<V, usize>,
    stack: &mut Vec<V>,
    on_stack: &mut HashSet<V>,
    components: &mut Vec<Vec<V>>,
    vertex_to_component: &mut HashMap<V, usize>,
) where
    V: Clone + Eq + Hash,
{
    // 设置顶点的index和lowlink
    indices.insert(vertex.clone(), *index);
    lowlinks.insert(vertex.clone(), *index);
    *index += 1;

    // 压入栈
    stack.push(vertex.clone());
    on_stack.insert(vertex.clone());

    // 遍历邻居
    if let Some(neighbors) = graph.get(vertex) {
        for neighbor in neighbors {
            if !indices.contains_key(neighbor) {
                // 邻居未访问，递归
                strong_connect(
                    graph,
                    neighbor,
                    index,
                    indices,
                    lowlinks,
                    stack,
                    on_stack,
                    components,
                    vertex_to_component,
                );

                // 更新lowlink
                let neighbor_low = *lowlinks.get(neighbor).unwrap();
                let vertex_low = lowlinks.get_mut(vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_low);
            } else if on_stack.contains(neighbor) {
                // 邻居在栈中，说明发现回边
                let neighbor_idx = *indices.get(neighbor).unwrap();
                let vertex_low = lowlinks.get_mut(vertex).unwrap();
                *vertex_low = (*vertex_low).min(neighbor_idx);
            }
        }
    }

    // 检查是否是SCC的根
    if lowlinks.get(vertex) == indices.get(vertex) {
        let mut component = Vec::new();
        let component_id = components.len();

        loop {
            let w = stack.pop().unwrap();
            on_stack.remove(&w);
            vertex_to_component.insert(w.clone(), component_id);
            component.push(w.clone());

            if &w == vertex {
                break;
            }
        }

        components.push(component);
    }
}

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

/// 检查图是否是强连通的
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::tarjan_scc::is_strongly_connected;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['C']);
/// graph.insert('C', vec!['A']);
///
/// assert!(is_strongly_connected(&graph));
/// ```
pub fn is_strongly_connected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    let result = tarjan_scc(graph);

    if result.count() != 1 {
        return false;
    }

    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    result.components[0].len() == all_vertices.len()
}

/// 获取所有源点分量（没有入边的SCC）
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn find_source_components<V>(result: &TarjanSCCResult<V>) -> Vec<usize>
where
    V: Clone + Eq + Hash,
{
    let n = result.count();
    let mut has_incoming = vec![false; n];

    for (from, to_set) in &result.condensed_graph {
        for to in to_set {
            has_incoming[*to] = true;
        }
    }

    has_incoming
        .iter()
        .enumerate()
        .filter_map(|(i, &has)| if !has { Some(i) } else { None })
        .collect()
}

/// 获取所有汇点分量（没有出边的SCC）
///
/// # 复杂度
/// - **时间**: O(V)
/// - **空间**: O(V)
pub fn find_sink_components<V>(result: &TarjanSCCResult<V>) -> Vec<usize>
where
    V: Clone + Eq + Hash,
{
    result
        .condensed_graph
        .iter()
        .filter_map(|(id, neighbors)| {
            if neighbors.is_empty() {
                Some(*id)
            } else {
                None
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 1);
        assert_eq!(result.components[0].len(), 3);
    }

    #[test]
    fn test_multiple_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1: A-B-C
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A', 'D']);
        // SCC 2: D-E
        graph.insert('D', vec!['E']);
        graph.insert('E', vec!['D']);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 2);
        assert!(result.same_component(&'A', &'B'));
        assert!(result.same_component(&'D', &'E'));
        assert!(!result.same_component(&'A', &'D'));
    }

    #[test]
    fn test_dag() {
        // 有向无环图，每个顶点是一个SCC
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['D']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec![]);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 4);
    }

    #[test]
    fn test_self_loop() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['A']);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 1);
        assert!(is_strongly_connected(&graph));
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 1);
        assert!(result.components[0].contains(&'A'));
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
        // 7单独一个SCC
        graph.insert(7, vec![]);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 3);
    }

    #[test]
    fn test_condensed_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1: A
        graph.insert('A', vec!['B']);
        // SCC 2: B
        graph.insert('B', vec!['C']);
        // SCC 3: C
        graph.insert('C', vec![]);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 3);

        // 检查缩点图: 0->1->2
        let source = find_source_components(&result);
        let sink = find_sink_components(&result);
        assert_eq!(source.len(), 1);
        assert_eq!(sink.len(), 1);
    }

    #[test]
    fn test_strongly_connected() {
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
    fn test_disconnected_components() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 组件1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        // 组件2（不相连）
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 2);
    }

    #[test]
    fn test_numerical_vertices() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        for i in 0..10 {
            graph.insert(i, vec![(i + 1) % 10]);
        }

        let result = tarjan_scc(&graph);
        assert_eq!(result.count(), 1);
        assert_eq!(result.components[0].len(), 10);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：社交网络社区发现
    pub fn social_network_example() {
        println!("=== Tarjan算法 - 社交网络社区发现 ===");

        let mut graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // 社区1：紧密互动的用户群
        graph.insert("Alice", vec!["Bob", "Carol"]);
        graph.insert("Bob", vec!["Alice", "Carol", "David"]);
        graph.insert("Carol", vec!["Alice", "Bob"]);
        // 社区2：另一个用户群
        graph.insert("David", vec!["Eve"]);
        graph.insert("Eve", vec!["David"]);
        // 孤立用户
        graph.insert("Frank", vec![]);

        let result = tarjan_scc(&graph);
        println!("发现 {} 个社区:", result.count());
        for (i, comp) in result.components.iter().enumerate() {
            println!("  社区 {}: {:?}", i + 1, comp);
        }
    }

    /// 示例：代码依赖分析
    pub fn dependency_analysis_example() {
        println!("\n=== Tarjan算法 - 代码模块依赖分析 ===");

        let mut graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // 循环依赖组1
        graph.insert("module_a", vec!["module_b"]);
        graph.insert("module_b", vec!["module_c"]);
        graph.insert("module_c", vec!["module_a", "utils"]);
        // 循环依赖组2
        graph.insert("utils", vec!["helpers"]);
        graph.insert("helpers", vec!["utils"]);

        let result = tarjan_scc(&graph);
        println!("代码模块分析:");
        for (i, comp) in result.components.iter().enumerate() {
            if comp.len() > 1 {
                println!("  循环依赖组 {}: {:?} ⚠️", i + 1, comp);
            } else {
                println!("  独立模块 {}: {:?}", i + 1, comp);
            }
        }
    }
}
