//! 拓扑排序 (Topological Sort)
//!
//! 拓扑排序是对有向无环图(DAG)的顶点进行线性排序，使得对于每条边(u, v)，
//! u在排序中都出现在v之前。
//!
//! # 算法实现
//! - **Kahn算法**: 基于入度的BFS方法
//! - **DFS算法**: 基于深度优先搜索的方法
//!
//! # 应用场景
//! - 任务调度（先决条件排序）
//! - 编译依赖解析
//! - 课程选修计划
//! - 数据处理管道
//!
//! # 复杂度分析
//! | 算法 | 时间复杂度 | 空间复杂度 | 特点 |
//! |------|-----------|-----------|------|
//! | Kahn | O(V + E) | O(V) | 自然检测环，可并行 |
//! | DFS | O(V + E) | O(V) | 代码简洁，递归实现 |

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

/// 拓扑排序结果
#[derive(Debug, Clone)]
pub struct TopologicalSortResult<V> {
    /// 拓扑序列表（如果存在）
    pub order: Option<Vec<V>>,
    /// 图中是否存在环
    pub has_cycle: bool,
    /// 每个顶点的入度（仅Kahn算法）
    pub in_degrees: Option<HashMap<V, usize>>,
}

impl<V> TopologicalSortResult<V> {
    /// 获取拓扑序，如果存在环则返回None
    pub fn get_order(&self) -> Option<&Vec<V>> {
        self.order.as_ref()
    }

    /// 检查是否存在有效的拓扑序
    pub fn is_valid(&self) -> bool {
        !self.has_cycle
    }
}

/// Kahn算法 - 基于入度的拓扑排序
///
/// # 算法说明
///
/// Kahn算法通过反复移除入度为0的顶点来构造拓扑序：
/// 1. 计算所有顶点的入度
/// 2. 将入度为0的顶点加入队列
/// 3. 依次取出顶点，将其邻接顶点入度减1
/// 4. 若邻接顶点入度变为0，加入队列
/// 5. 重复直到队列为空
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 计算入度: O(E)
///   - 每个顶点入队出队一次: O(V)
///   - 每条边被处理一次: O(E)
///
/// - **空间复杂度**: O(V)
///   - 入度数组: O(V)
///   - 队列: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图
///
/// # 返回值
///
/// 返回 `TopologicalSortResult`，包含：
/// - `order`: 拓扑序（如果无环）
/// - `has_cycle`: 是否存在环
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::topological_sort::topological_sort_kahn;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['C']);
/// graph.insert('B', vec!['C', 'D']);
/// graph.insert('C', vec!['E']);
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec![]);
///
/// let result = topological_sort_kahn(&graph);
/// assert!(result.is_valid());
/// let order = result.get_order().unwrap();
///
/// // 验证拓扑序: A和B在C之前，C在E之前
/// let pos = |c| order.iter().position(|&x| x == c).unwrap();
/// assert!(pos('A') < pos('C'));
/// assert!(pos('B') < pos('C'));
/// assert!(pos('C') < pos('E'));
/// ```
pub fn topological_sort_kahn<V>(graph: &HashMap<V, Vec<V>>) -> TopologicalSortResult<V>
where
    V: Clone + Eq + Hash,
{
    // 计算入度
    let mut in_degree: HashMap<V, usize> = HashMap::new();

    // 初始化所有顶点的入度为0
    for (vertex, _) in graph.iter() {
        in_degree.entry(vertex.clone()).or_insert(0);
    }

    // 计算入度
    for (_, neighbors) in graph.iter() {
        for neighbor in neighbors {
            *in_degree.entry(neighbor.clone()).or_insert(0) += 1;
        }
    }

    // 将所有入度为0的顶点加入队列
    let mut queue: VecDeque<V> = in_degree
        .iter()
        .filter(|(_, &degree)| degree == 0)
        .map(|(v, _)| v.clone())
        .collect();

    let mut result = Vec::new();

    while let Some(vertex) = queue.pop_front() {
        result.push(vertex.clone());

        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                if let Some(degree) = in_degree.get_mut(neighbor) {
                    *degree -= 1;
                    if *degree == 0 {
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }
    }

    // 检查是否存在环
    let has_cycle = result.len() != in_degree.len();

    TopologicalSortResult {
        order: if has_cycle { None } else { Some(result) },
        has_cycle,
        in_degrees: Some(in_degree),
    }
}

/// DFS算法 - 基于深度优先搜索的拓扑排序
///
/// # 算法说明
///
/// DFS拓扑排序利用DFS的完成时间顺序：
/// 1. 对图进行DFS遍历
/// 2. 当顶点所有邻接顶点都访问完成后，将该顶点加入结果
/// 3. 最后将结果反转即得拓扑序
///
/// 若DFS过程中遇到已访问但未完成的顶点，则存在环。
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 每个顶点访问一次: O(V)
///   - 每条边检查一次: O(E)
///
/// - **空间复杂度**: O(V)
///   - 递归栈: O(V)
///   - 访问标记: O(V)
///
/// # 参数
///
/// * `graph` - 邻接表表示的有向图
///
/// # 返回值
///
/// 返回 `TopologicalSortResult`
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::topological_sort::topological_sort_dfs;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['C', 'D']);
/// graph.insert('B', vec!['D']);
/// graph.insert('C', vec!['E']);
/// graph.insert('D', vec!['E']);
/// graph.insert('E', vec![]);
///
/// let result = topological_sort_dfs(&graph);
/// assert!(result.is_valid());
/// ```
pub fn topological_sort_dfs<V>(graph: &HashMap<V, Vec<V>>) -> TopologicalSortResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut visited: HashSet<V> = HashSet::new();
    let mut temp_mark: HashSet<V> = HashSet::new(); // 用于检测环
    let mut result: Vec<V> = Vec::new();
    let mut has_cycle = false;

    // 收集所有顶点
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    for vertex in &all_vertices {
        if !visited.contains(vertex) {
            if dfs_visit(
                graph,
                vertex.clone(),
                &mut visited,
                &mut temp_mark,
                &mut result,
            ) {
                has_cycle = true;
                break;
            }
        }
    }

    if has_cycle {
        TopologicalSortResult {
            order: None,
            has_cycle: true,
            in_degrees: None,
        }
    } else {
        result.reverse();
        TopologicalSortResult {
            order: Some(result),
            has_cycle: false,
            in_degrees: None,
        }
    }
}

fn dfs_visit<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    visited: &mut HashSet<V>,
    temp_mark: &mut HashSet<V>,
    result: &mut Vec<V>,
) -> bool
where
    V: Clone + Eq + Hash,
{
    // 发现环
    if temp_mark.contains(&vertex) {
        return true;
    }

    // 已处理完成
    if visited.contains(&vertex) {
        return false;
    }

    temp_mark.insert(vertex.clone());

    // 递归访问邻接顶点
    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if dfs_visit(graph, neighbor.clone(), visited, temp_mark, result) {
                return true;
            }
        }
    }

    temp_mark.remove(&vertex);
    visited.insert(vertex.clone());
    result.push(vertex);

    false
}

/// 检测有向图是否存在环
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::topological_sort::has_cycle;
///
/// // 无环图
/// let mut dag: HashMap<char, Vec<char>> = HashMap::new();
/// dag.insert('A', vec!['B']);
/// dag.insert('B', vec!['C']);
/// dag.insert('C', vec![]);
/// assert!(!has_cycle(&dag));
///
/// // 有环图
/// let mut cyclic: HashMap<char, Vec<char>> = HashMap::new();
/// cyclic.insert('A', vec!['B']);
/// cyclic.insert('B', vec!['C']);
/// cyclic.insert('C', vec!['A']);
/// assert!(has_cycle(&cyclic));
/// ```
pub fn has_cycle<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    topological_sort_kahn(graph).has_cycle
}

/// 获取图中所有源点（入度为0的顶点）
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn get_sources<V>(graph: &HashMap<V, Vec<V>>) -> Vec<V>
where
    V: Clone + Eq + Hash,
{
    let mut in_degree: HashMap<V, usize> = HashMap::new();

    for (vertex, _) in graph.iter() {
        in_degree.entry(vertex.clone()).or_insert(0);
    }

    for (_, neighbors) in graph.iter() {
        for neighbor in neighbors {
            *in_degree.entry(neighbor.clone()).or_insert(0) += 1;
        }
    }

    in_degree
        .into_iter()
        .filter(|(_, degree)| *degree == 0)
        .map(|(v, _)| v)
        .collect()
}

/// 获取图中所有汇点（出度为0的顶点）
///
/// # 复杂度
/// - **时间**: O(V)
/// - **空间**: O(V)
pub fn get_sinks<V>(graph: &HashMap<V, Vec<V>>) -> Vec<V>
where
    V: Clone + Eq + Hash,
{
    graph
        .iter()
        .filter(|(_, neighbors)| neighbors.is_empty())
        .map(|(v, _)| v.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_dag() -> HashMap<char, Vec<char>> {
        let mut graph = HashMap::new();
        graph.insert('A', vec!['C']);
        graph.insert('B', vec!['C', 'D']);
        graph.insert('C', vec!['E']);
        graph.insert('D', vec!['E']);
        graph.insert('E', vec![]);
        graph
    }

    fn create_cyclic_graph() -> HashMap<char, Vec<char>> {
        let mut graph = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);
        graph
    }

    #[test]
    fn test_kahn_basic() {
        let graph = create_dag();
        let result = topological_sort_kahn(&graph);

        assert!(result.is_valid());
        let order = result.get_order().unwrap();

        // 验证拓扑序约束
        let pos = |c| order.iter().position(|&x| x == c).unwrap();
        assert!(pos('A') < pos('C'));
        assert!(pos('B') < pos('C'));
        assert!(pos('B') < pos('D'));
        assert!(pos('C') < pos('E'));
        assert!(pos('D') < pos('E'));
    }

    #[test]
    fn test_kahn_cycle_detection() {
        let graph = create_cyclic_graph();
        let result = topological_sort_kahn(&graph);

        assert!(!result.is_valid());
        assert!(result.has_cycle);
        assert!(result.get_order().is_none());
    }

    #[test]
    fn test_dfs_basic() {
        let graph = create_dag();
        let result = topological_sort_dfs(&graph);

        assert!(result.is_valid());
        let order = result.get_order().unwrap();

        let pos = |c| order.iter().position(|&x| x == c).unwrap();
        assert!(pos('A') < pos('C'));
        assert!(pos('B') < pos('C'));
        assert!(pos('B') < pos('D'));
        assert!(pos('C') < pos('E'));
    }

    #[test]
    fn test_dfs_cycle_detection() {
        let graph = create_cyclic_graph();
        let result = topological_sort_dfs(&graph);

        assert!(!result.is_valid());
        assert!(result.has_cycle);
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = topological_sort_kahn(&graph);

        assert!(result.is_valid());
        assert_eq!(result.get_order().unwrap().len(), 0);
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = topological_sort_kahn(&graph);
        assert!(result.is_valid());
        assert_eq!(result.get_order().unwrap().clone(), vec!['A']);
    }

    #[test]
    fn test_self_loop() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['A']);

        let result = topological_sort_kahn(&graph);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_disconnected_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec![]);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec![]);

        let result = topological_sort_kahn(&graph);
        assert!(result.is_valid());

        let order = result.get_order().unwrap();
        assert_eq!(order.len(), 4);

        let pos = |c| order.iter().position(|&x| x == c).unwrap();
        assert!(pos('A') < pos('B'));
        assert!(pos('C') < pos('D'));
    }

    #[test]
    fn test_has_cycle_function() {
        let dag = create_dag();
        let cyclic = create_cyclic_graph();

        assert!(!has_cycle(&dag));
        assert!(has_cycle(&cyclic));
    }

    #[test]
    fn test_get_sources() {
        let graph = create_dag();
        let sources = get_sources(&graph);

        assert_eq!(sources.len(), 2);
        assert!(sources.contains(&'A'));
        assert!(sources.contains(&'B'));
    }

    #[test]
    fn test_get_sinks() {
        let graph = create_dag();
        let sinks = get_sinks(&graph);

        assert_eq!(sinks.len(), 1);
        assert!(sinks.contains(&'E'));
    }

    #[test]
    fn test_linear_chain() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2]);
        graph.insert(2, vec![3]);
        graph.insert(3, vec![4]);
        graph.insert(4, vec![5]);
        graph.insert(5, vec![]);

        let result = topological_sort_kahn(&graph);
        assert!(result.is_valid());

        let order = result.get_order().unwrap();
        assert_eq!(order.clone(), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_diamond_graph() {
        // 菱形图: A -> B -> D, A -> C -> D
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['D']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec![]);

        let result = topological_sort_kahn(&graph);
        assert!(result.is_valid());

        let order = result.get_order().unwrap();
        let pos = |c| order.iter().position(|&x| x == c).unwrap();

        assert_eq!(pos('A'), 0); // A必须是第一个
        assert_eq!(pos('D'), 3); // D必须是最后一个
    }

    #[test]
    fn test_large_graph() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();

        // 构建一个较大的DAG: i -> i+1, i -> i+2
        for i in 0..100 {
            let mut neighbors = vec![];
            if i + 1 < 100 {
                neighbors.push(i + 1);
            }
            if i + 2 < 100 {
                neighbors.push(i + 2);
            }
            graph.insert(i, neighbors);
        }

        let result = topological_sort_kahn(&graph);
        assert!(result.is_valid());

        // 验证所有边都满足拓扑序
        let order = result.get_order().unwrap();
        let positions: HashMap<i32, usize> = order
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, i))
            .collect();

        for i in 0..100 {
            if let Some(neighbors) = graph.get(&i) {
                for &neighbor in neighbors {
                    assert!(positions[&i] < positions[&neighbor]);
                }
            }
        }
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 课程选修计划
    pub fn example_course_schedule() {
        println!("=== 课程选修计划示例 ===");

        let mut prerequisites: HashMap<&str, Vec<&str>> = HashMap::new();
        prerequisites.insert("高级算法", vec!["数据结构", "算法基础"]);
        prerequisites.insert("机器学习", vec!["概率论", "线性代数", "Python编程"]);
        prerequisites.insert("数据结构", vec!["编程基础"]);
        prerequisites.insert("算法基础", vec!["编程基础", "数据结构"]);
        prerequisites.insert("概率论", vec!["高等数学"]);
        prerequisites.insert("线性代数", vec!["高等数学"]);
        prerequisites.insert("Python编程", vec!["编程基础"]);
        prerequisites.insert("编程基础", vec![]);
        prerequisites.insert("高等数学", vec![]);

        let result = topological_sort_kahn(&prerequisites);

        if let Some(order) = result.get_order() {
            println!("推荐学习顺序:");
            for (i, course) in order.iter().enumerate() {
                println!("  {}. {}", i + 1, course);
            }
        } else {
            println!("课程依赖存在循环，无法制定学习计划!");
        }
    }

    /// 示例2: 编译依赖解析
    pub fn example_build_dependencies() {
        println!("\n=== 编译依赖解析示例 ===");

        let mut dependencies: HashMap<&str, Vec<&str>> = HashMap::new();
        dependencies.insert("main.exe", vec!["libmath.a", "libio.a"]);
        dependencies.insert("libmath.a", vec!["math.o", "utils.o"]);
        dependencies.insert("libio.a", vec!["io.o", "utils.o"]);
        dependencies.insert("math.o", vec!["math.cpp"]);
        dependencies.insert("io.o", vec!["io.cpp"]);
        dependencies.insert("utils.o", vec!["utils.cpp"]);
        dependencies.insert("math.cpp", vec![]);
        dependencies.insert("io.cpp", vec![]);
        dependencies.insert("utils.cpp", vec![]);

        let result = topological_sort_kahn(&dependencies);

        if let Some(order) = result.get_order() {
            println!("编译顺序（从源文件到目标文件）:");
            for item in order {
                println!("  -> {}", item);
            }
        }
    }

    /// 示例3: 任务调度
    pub fn example_task_scheduling() {
        println!("\n=== 任务调度示例 ===");

        let mut tasks: HashMap<&str, Vec<&str>> = HashMap::new();
        tasks.insert("部署应用", vec!["运行测试", "构建镜像"]);
        tasks.insert("运行测试", vec!["编译代码"]);
        tasks.insert("构建镜像", vec!["编译代码"]);
        tasks.insert("编译代码", vec!["安装依赖", "代码检查"]);
        tasks.insert("安装依赖", vec!["检出代码"]);
        tasks.insert("代码检查", vec!["检出代码"]);
        tasks.insert("检出代码", vec![]);

        let result = topological_sort_kahn(&tasks);

        if let Some(order) = result.get_order() {
            println!("CI/CD流水线执行顺序:");
            for (i, task) in order.iter().enumerate() {
                println!("  步骤 {}: {}", i + 1, task);
            }
        }
    }
}
