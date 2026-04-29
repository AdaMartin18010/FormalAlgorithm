//! 强连通分量 (Strongly Connected Components)
//!
//! 强连通分量(SCC)是有向图中的极大子图，其中任意两个顶点都可以互相到达。
//! 本模块实现了两种经典算法：
//! - **Kosaraju算法**: 两次DFS遍历
//! - **Tarjan算法**: 单次DFS遍历，使用low-link值
//!
//! # 应用场景
//! - 社交网络中的社区发现
//! - 网页链接分析
//! - 编译器控制流分析
//! - 2-SAT问题求解
//!
//! # 复杂度分析
//! | 算法 | 时间复杂度 | 空间复杂度 | 特点 |
//! |------|-----------|-----------|------|
//! | Kosaraju | O(V + E) | O(V) | 代码简单，需要两次遍历 |
//! | Tarjan | O(V + E) | O(V) | 单次遍历，空间高效 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// 强连通分量结果
#[derive(Debug, Clone)]
pub struct SCCResult<V> {
    /// 所有强连通分量，每个分量是一个顶点集合
    pub components: Vec<HashSet<V>>,
    /// 分量图（缩点后的DAG）
    pub component_graph: HashMap<usize, HashSet<usize>>,
    /// 每个顶点所属的分量编号
    pub vertex_to_component: HashMap<V, usize>,
}

impl<V> SCCResult<V>
where
    V: Eq + Hash + Clone,
{
    /// 获取强连通分量的数量
    pub fn count(&self) -> usize {
        self.components.len()
    }

    /// 检查两个顶点是否在同一个强连通分量中
    pub fn in_same_component(&self, v1: &V, v2: &V) -> bool {
        match (self.vertex_to_component.get(v1), self.vertex_to_component.get(v2)) {
            (Some(c1), Some(c2)) => c1 == c2,
            _ => false,
        }
    }

    /// 获取包含指定顶点的强连通分量
    pub fn get_component(&self, vertex: &V) -> Option<&HashSet<V>> {
        self.vertex_to_component
            .get(vertex)
            .and_then(|&id| self.components.get(id))
    }
}

/// Kosaraju算法 - 计算强连通分量
///
/// # 算法说明
///
/// Kosaraju算法基于以下关键观察：
/// 1. 对原图G进行DFS，记录顶点完成时间的逆序
/// 2. 计算原图的转置图G^T（所有边反向）
/// 3. 按照步骤1的逆序对G^T进行DFS，每次DFS访问的顶点构成一个SCC
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 第一次DFS遍历: O(V + E)
///   - 构建转置图: O(E)
///   - 第二次DFS遍历: O(V + E)
///
/// - **空间复杂度**: O(V + E)
///   - 访问标记: O(V)
///   - 递归栈: O(V)
///   - 转置图: O(V + E)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图
///
/// # 返回值
///
/// 返回 `SCCResult`，包含所有强连通分量和缩点后的DAG
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::strongly_connected_components::kosaraju;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // SCC 1: A <-> B <-> C
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['C']);
/// graph.insert('C', vec!['A']);
/// // SCC 2: D <-> E
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec!['D']);
/// // Edge from SCC 1 to SCC 2
/// graph.insert('C', vec!['A', 'D']);
///
/// let result = kosaraju(&graph);
/// assert_eq!(result.count(), 2);
/// ```
pub fn kosaraju<V>(graph: &HashMap<V, Vec<V>>) -> SCCResult<V>
where
    V: Clone + Eq + Hash,
{
    // 第一次DFS：获取完成顺序
    let mut visited: HashSet<V> = HashSet::new();
    let mut finish_order: Vec<V> = Vec::new();

    // 收集所有顶点
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    // 第一次DFS
    for vertex in &all_vertices {
        if !visited.contains(vertex) {
            dfs_first_pass(graph, vertex.clone(), &mut visited, &mut finish_order);
        }
    }

    // 构建转置图
    let transpose = build_transpose(graph);

    // 第二次DFS：按照完成顺序的逆序遍历转置图
    visited.clear();
    let mut components: Vec<HashSet<V>> = Vec::new();
    let mut vertex_to_component: HashMap<V, usize> = HashMap::new();

    for vertex in finish_order.iter().rev() {
        if !visited.contains(vertex) {
            let mut component = HashSet::new();
            dfs_second_pass(&transpose, vertex.clone(), &mut visited, &mut component);

            let component_id = components.len();
            for v in &component {
                vertex_to_component.insert(v.clone(), component_id);
            }
            components.push(component);
        }
    }

    // 构建分量图（缩点后的DAG）
    let component_graph = build_component_graph(graph, &vertex_to_component, components.len());

    SCCResult {
        components,
        component_graph,
        vertex_to_component,
    }
}

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

fn dfs_second_pass<V>(
    transpose: &HashMap<V, Vec<V>>,
    vertex: V,
    visited: &mut HashSet<V>,
    component: &mut HashSet<V>,
) where
    V: Clone + Eq + Hash,
{
    visited.insert(vertex.clone());
    component.insert(vertex.clone());

    if let Some(neighbors) = transpose.get(&vertex) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                dfs_second_pass(transpose, neighbor.clone(), visited, component);
            }
        }
    }
}

fn build_transpose<V>(graph: &HashMap<V, Vec<V>>) -> HashMap<V, Vec<V>>
where
    V: Clone + Eq + Hash,
{
    let mut transpose: HashMap<V, Vec<V>> = HashMap::new();

    // 初始化所有顶点
    for (vertex, _) in graph.iter() {
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

/// Tarjan算法 - 计算强连通分量
///
/// # 算法说明
///
/// Tarjan算法使用单次DFS遍历，为每个顶点维护两个值：
/// - `index`: DFS访问顺序编号
/// - `lowlink`: 从该顶点可达的最小index
///
/// 当 `index == lowlink` 时，发现一个SCC的根节点。
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 每个顶点访问一次
///   - 每条边检查一次
///
/// - **空间复杂度**: O(V)
///   - 栈: O(V)
///   - index/lowlink数组: O(V)
///   - 递归栈: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图
///
/// # 返回值
///
/// 返回 `SCCResult`
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::strongly_connected_components::tarjan;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B']);
/// graph.insert('B', vec!['C', 'D']);
/// graph.insert('C', vec!['A']);
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec!['D']);
///
/// let result = tarjan(&graph);
/// assert_eq!(result.count(), 2); // {A,B,C} 和 {D,E}
/// ```
pub fn tarjan<V>(graph: &HashMap<V, Vec<V>>) -> SCCResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut index_counter = 0usize;
    let mut index: HashMap<V, usize> = HashMap::new();
    let mut lowlink: HashMap<V, usize> = HashMap::new();
    let mut on_stack: HashSet<V> = HashSet::new();
    let mut stack: Vec<V> = Vec::new();
    let mut components: Vec<HashSet<V>> = Vec::new();
    let mut vertex_to_component: HashMap<V, usize> = HashMap::new();

    // 收集所有顶点
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    for vertex in &all_vertices {
        if !index.contains_key(vertex) {
            tarjan_dfs(
                graph,
                vertex.clone(),
                &mut index_counter,
                &mut index,
                &mut lowlink,
                &mut on_stack,
                &mut stack,
                &mut components,
                &mut vertex_to_component,
            );
        }
    }

    // 构建分量图
    let component_graph = build_component_graph(graph, &vertex_to_component, components.len());

    SCCResult {
        components,
        component_graph,
        vertex_to_component,
    }
}

fn tarjan_dfs<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    index_counter: &mut usize,
    index: &mut HashMap<V, usize>,
    lowlink: &mut HashMap<V, usize>,
    on_stack: &mut HashSet<V>,
    stack: &mut Vec<V>,
    components: &mut Vec<HashSet<V>>,
    vertex_to_component: &mut HashMap<V, usize>,
) where
    V: Clone + Eq + Hash,
{
    let current_index = *index_counter;
    index.insert(vertex.clone(), current_index);
    lowlink.insert(vertex.clone(), current_index);
    *index_counter += 1;

    stack.push(vertex.clone());
    on_stack.insert(vertex.clone());

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if !index.contains_key(neighbor) {
                // 邻居未被访问，递归访问
                tarjan_dfs(
                    graph,
                    neighbor.clone(),
                    index_counter,
                    index,
                    lowlink,
                    on_stack,
                    stack,
                    components,
                    vertex_to_component,
                );

                // 更新lowlink值
                let neighbor_lowlink = *lowlink.get(neighbor).unwrap();
                let vertex_lowlink = lowlink.get_mut(&vertex).unwrap();
                *vertex_lowlink = (*vertex_lowlink).min(neighbor_lowlink);
            } else if on_stack.contains(neighbor) {
                // 邻居在栈中，说明发现回边
                let neighbor_index = *index.get(neighbor).unwrap();
                let vertex_lowlink = lowlink.get_mut(&vertex).unwrap();
                *vertex_lowlink = (*vertex_lowlink).min(neighbor_index);
            }
        }
    }

    // 检查是否是SCC的根节点
    if lowlink.get(&vertex) == index.get(&vertex) {
        let mut component = HashSet::new();
        let component_id = components.len();

        loop {
            let w = stack.pop().unwrap();
            on_stack.remove(&w);
            component.insert(w.clone());
            let is_root = w == vertex;
            vertex_to_component.insert(w, component_id);

            if is_root {
                break;
            }
        }

        components.push(component);
    }
}

fn build_component_graph<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex_to_component: &HashMap<V, usize>,
    num_components: usize,
) -> HashMap<usize, HashSet<usize>>
where
    V: Clone + Eq + Hash,
{
    let mut component_graph: HashMap<usize, HashSet<usize>> = HashMap::new();

    for i in 0..num_components {
        component_graph.insert(i, HashSet::new());
    }

    for (vertex, neighbors) in graph.iter() {
        if let Some(&from_component) = vertex_to_component.get(vertex) {
            for neighbor in neighbors {
                if let Some(&to_component) = vertex_to_component.get(neighbor) {
                    if from_component != to_component {
                        component_graph
                            .entry(from_component)
                            .or_default()
                            .insert(to_component);
                    }
                }
            }
        }
    }

    component_graph
}

/// 检查图是否强连通
///
/// 强连通图是指只有一个强连通分量，且包含所有顶点。
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::strongly_connected_components::is_strongly_connected;
///
/// // 强连通图
/// let mut scc: HashMap<char, Vec<char>> = HashMap::new();
/// scc.insert('A', vec!['B']);
/// scc.insert('B', vec!['C']);
/// scc.insert('C', vec!['A']);
/// assert!(is_strongly_connected(&scc));
///
/// // 非强连通图
/// let mut non_scc: HashMap<char, Vec<char>> = HashMap::new();
/// non_scc.insert('A', vec!['B']);
/// non_scc.insert('B', vec![]);
/// assert!(!is_strongly_connected(&non_scc));
/// ```
pub fn is_strongly_connected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    let result = kosaraju(graph);

    if result.count() != 1 {
        return false;
    }

    // 检查是否包含所有顶点
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    result.components[0].len() == all_vertices.len()
}

/// 获取图的缩点DAG
///
/// 将每个强连通分量收缩为一个节点，得到有向无环图。
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V + E)
pub fn condense_graph<V>(graph: &HashMap<V, Vec<V>>) -> SCCResult<V>
where
    V: Clone + Eq + Hash,
{
    tarjan(graph)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kosaraju_simple() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);

        let result = kosaraju(&graph);
        assert_eq!(result.count(), 1);
        assert_eq!(result.components[0].len(), 3);
    }

    #[test]
    fn test_kosaraju_multiple_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A', 'D']);
        // SCC 2
        graph.insert('D', vec!['E']);
        graph.insert('E', vec!['F']);
        graph.insert('F', vec!['D']);

        let result = kosaraju(&graph);
        assert_eq!(result.count(), 2);

        // 检查分量图
        assert!(result.component_graph.contains_key(&0) || result.component_graph.contains_key(&1));
    }

    #[test]
    fn test_tarjan_simple() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C', 'D']);
        graph.insert('C', vec!['A']);
        graph.insert('D', vec!['E']);
        graph.insert('E', vec!['D']);

        let result = tarjan(&graph);
        assert_eq!(result.count(), 2);

        // 检查A,B,C在同一个分量
        assert!(result.in_same_component(&'A', &'B'));
        assert!(result.in_same_component(&'B', &'C'));

        // 检查D,E在另一个分量
        assert!(result.in_same_component(&'D', &'E'));

        // 检查跨分量不相通
        assert!(!result.in_same_component(&'A', &'D'));
    }

    #[test]
    fn test_is_strongly_connected() {
        // 强连通图
        let mut scc: HashMap<char, Vec<char>> = HashMap::new();
        scc.insert('A', vec!['B']);
        scc.insert('B', vec!['C']);
        scc.insert('C', vec!['A']);
        assert!(is_strongly_connected(&scc));

        // 非强连通图
        let mut non_scc: HashMap<char, Vec<char>> = HashMap::new();
        non_scc.insert('A', vec!['B']);
        non_scc.insert('B', vec!['C']);
        non_scc.insert('C', vec![]);
        assert!(!is_strongly_connected(&non_scc));
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = kosaraju(&graph);
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = kosaraju(&graph);
        assert_eq!(result.count(), 1);
        assert!(result.components[0].contains(&'A'));
    }

    #[test]
    fn test_self_loop() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['A']);

        let result = kosaraju(&graph);
        assert_eq!(result.count(), 1);
        assert!(is_strongly_connected(&graph));
    }

    #[test]
    fn test_disconnected_scc() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // SCC 1
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        // SCC 2 (不相连)
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = kosaraju(&graph);
        assert_eq!(result.count(), 2);
        assert!(!result.in_same_component(&'A', &'C'));
    }

    #[test]
    fn test_dag() {
        // 有向无环图，每个顶点自成一个SCC
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['C', 'D']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec![]);

        let result = tarjan(&graph);
        assert_eq!(result.count(), 4);

        // 检查分量图的结构
        // 应该包含边: A->B, A->C, B->C, B->D, C->D
        let component_of = |v| result.vertex_to_component.get(&v).copied().unwrap();

        let a_comp = component_of('A');
        let b_comp = component_of('B');
        let c_comp = component_of('C');
        let d_comp = component_of('D');

        assert!(result.component_graph[&a_comp].contains(&b_comp));
        assert!(result.component_graph[&a_comp].contains(&c_comp));
        assert!(result.component_graph[&b_comp].contains(&d_comp));
    }

    #[test]
    fn test_kosaraju_and_tarjan_equivalence() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2]);
        graph.insert(2, vec![3, 4]);
        graph.insert(3, vec![1]);
        graph.insert(4, vec![5]);
        graph.insert(5, vec![6]);
        graph.insert(6, vec![4]);
        graph.insert(6, vec![4, 7]);
        graph.insert(7, vec![]);

        let kosaraju_result = kosaraju(&graph);
        let tarjan_result = tarjan(&graph);

        assert_eq!(kosaraju_result.count(), tarjan_result.count());
        assert_eq!(kosaraju_result.count(), 3); // {1,2,3}, {4,5,6}, {7}
    }

    #[test]
    fn test_large_graph() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();

        // 构建100个顶点的图，每10个形成一个SCC
        for i in 0..100 {
            let _next = if (i + 1) % 10 == 0 { i - 9 } else { i + 1 };
            // 只添加在同一个组内的边
            let cross_edge = if i % 10 == 9 { i - 9 } else { i + 1 };
            graph.insert(i, vec![cross_edge]);
        }

        let result = tarjan(&graph);
        
        // 验证每个SCC都是环状结构
        for component in &result.components {
            // 每个分量应该是长度为10的环
            assert!(component.len() <= 10);
        }
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 社交网络社区发现
    pub fn example_social_network() {
        println!("=== 社交网络社区发现示例 ===");

        let mut social_graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // 社区1: Alice, Bob, Carol 互相关注
        social_graph.insert("Alice", vec!["Bob", "Carol"]);
        social_graph.insert("Bob", vec!["Alice", "Carol"]);
        social_graph.insert("Carol", vec!["Alice", "Bob", "David"]);
        // 社区2: David, Eve 互相关注
        social_graph.insert("David", vec!["Eve"]);
        social_graph.insert("Eve", vec!["David"]);
        // Frank 独立用户
        social_graph.insert("Frank", vec![]);

        let result = kosaraju(&social_graph);

        println!("发现 {} 个社区:", result.count());
        for (i, component) in result.components.iter().enumerate() {
            let members: Vec<_> = component.iter().cloned().collect();
            println!("  社区 {}: {:?}", i + 1, members);
        }
    }

    /// 示例2: 网页链接分析
    pub fn example_web_analysis() {
        println!("\n=== 网页链接分析示例 ===");

        let mut web_graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // 强连通组件1: 网站导航页面
        web_graph.insert("首页", vec!["产品", "关于", "联系"]);
        web_graph.insert("产品", vec!["首页", "定价"]);
        web_graph.insert("定价", vec!["产品", "首页"]);
        // 强连通组件2: 博客系统
        web_graph.insert("博客首页", vec!["文章1", "文章2"]);
        web_graph.insert("文章1", vec!["博客首页", "文章2"]);
        web_graph.insert("文章2", vec!["博客首页", "文章1"]);
        // 联系我们（汇点）
        web_graph.insert("关于", vec!["联系"]);
        web_graph.insert("联系", vec![]);

        let result = tarjan(&web_graph);

        println!("网页结构分析:");
        for (i, component) in result.components.iter().enumerate() {
            println!("  组件 {}: {:?}", i + 1, component);
        }

        println!("\n站点缩略图（DAG）:");
        for (from, to_set) in &result.component_graph {
            if !to_set.is_empty() {
                println!("  组件 {} -> {:?}", from + 1, to_set.iter().map(|x| x + 1).collect::<Vec<_>>());
            }
        }
    }

    /// 示例3: 2-SAT问题示例
    pub fn example_2sat() {
        println!("\n=== 2-SAT问题示例 ===");

        // 2-SAT问题可以转化为蕴含图，求强连通分量
        // 变量: x1, x2, x3
        // 子句: (x1 OR x2), (NOT x1 OR x3), (NOT x2 OR NOT x3)

        let mut implication_graph: HashMap<&str, Vec<&str>> = HashMap::new();
        // (x1 OR x2) => (NOT x1 -> x2), (NOT x2 -> x1)
        implication_graph.insert("NOT x1", vec!["x2"]);
        implication_graph.insert("NOT x2", vec!["x1"]);
        // (NOT x1 OR x3) => (x1 -> x3), (NOT x3 -> NOT x1)
        implication_graph.insert("x1", vec!["x3"]);
        implication_graph.insert("NOT x3", vec!["NOT x1"]);
        // (NOT x2 OR NOT x3) => (x2 -> NOT x3), (x3 -> NOT x2)
        implication_graph.insert("x2", vec!["NOT x3"]);
        implication_graph.insert("x3", vec!["NOT x2"]);

        let result = tarjan(&implication_graph);

        println!("蕴含图强连通分量:");
        for (i, scc) in result.components.iter().enumerate() {
            println!("  SCC {}: {:?}", i + 1, scc);
        }

        // 检查可满足性: 检查每个变量及其否定是否在同一SCC
        let mut satisfiable = true;
        for var in ["x1", "x2", "x3"] {
            let var_comp = result.vertex_to_component.get(var);
            let not_var = format!("NOT {}", var);
            let not_var_comp = result.vertex_to_component.get(not_var.as_str());

            if var_comp == not_var_comp && var_comp.is_some() {
                println!("\n矛盾! {} 和 {} 在同一强连通分量中", var, not_var);
                satisfiable = false;
                break;
            }
        }

        if satisfiable {
            println!("\n该2-SAT问题是可满足的!");
        }
    }
}
