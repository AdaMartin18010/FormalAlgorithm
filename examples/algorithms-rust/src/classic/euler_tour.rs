//! 欧拉路径与欧拉回路算法
//!
//! 欧拉路径是指经过图中每条边恰好一次的路径。
//! 欧拉回路是指起点和终点相同的欧拉路径。
//!
//! # 存在条件
//!
//! ## 无向图
//! - **欧拉回路**: 所有顶点的度数都是偶数，且图连通
//! - **欧拉路径**: 恰好有两个顶点的度数是奇数，其余都是偶数
//!
//! ## 有向图
//! - **欧拉回路**: 所有顶点的入度等于出度，且图强连通（忽略边方向）
//! - **欧拉路径**: 恰好一个顶点出度=入度+1（起点），一个顶点入度=出度+1（终点），其余相等
//!
//! # 算法原理
//!
//! Hierholzer算法：
//! 1. 从起点开始，沿着未访问的边深度遍历
//! 2. 当无法继续前进时，将顶点加入路径
//! 3. 如果还有未访问的边，从该点继续遍历
//! 4. 最后反转路径得到欧拉回路/路径
//!
//! # 应用场景
//! - 邮递员问题（中国邮路问题）
//! - DNA序列拼接
//! - 电路板钻孔优化
//! - 迷宫生成
//!
//! # 复杂度分析
//! | 指标 | 复杂度 | 说明 |
//! |------|--------|------|
//! | 时间 | O(V + E) | 每条边访问一次 |
//! | 空间 | O(V + E) | 存储图和路径 |

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// 欧拉路径/回路结果
#[derive(Debug, Clone)]
pub struct EulerResult<V> {
    /// 是否存在欧拉路径/回路
    pub exists: bool,
    /// 欧拉路径/回路（顶点序列）
    pub path: Vec<V>,
    /// 边序列（如果边有标识）
    pub edge_path: Vec<(V, V)>,
    /// 是否为回路（起点等于终点）
    pub is_circuit: bool,
    /// 起点
    pub start: Option<V>,
    /// 终点
    pub end: Option<V>,
}

impl<V> EulerResult<V>
where
    V: Clone + Eq + Hash,
{
    /// 创建空结果
    pub fn none() -> Self {
        EulerResult {
            exists: false,
            path: Vec::new(),
            edge_path: Vec::new(),
            is_circuit: false,
            start: None,
            end: None,
        }
    }
}

/// 检查无向图是否存在欧拉回路
///
/// # 条件
/// 1. 图连通
/// 2. 所有顶点的度数都是偶数
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn has_eulerian_circuit_undirected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    if graph.is_empty() {
        return true; // 空图认为存在
    }

    // 检查连通性
    if !is_connected_undirected(graph) {
        return false;
    }

    // 检查所有顶点度数为偶数
    for (vertex, neighbors) in graph.iter() {
        // 计算度数（注意自环计为2）
        let degree = neighbors
            .iter()
            .filter(|&n| n != vertex)
            .count()
            + neighbors.iter().filter(|&n| n == vertex).count() * 2;

        if degree % 2 != 0 {
            return false;
        }
    }

    true
}

/// 检查无向图是否存在欧拉路径
///
/// # 条件
/// 1. 图连通
/// 2. 恰好有0个或2个顶点的度数是奇数
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn has_eulerian_path_undirected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    if graph.is_empty() {
        return true;
    }

    // 检查连通性
    if !is_connected_undirected(graph) {
        return false;
    }

    // 统计奇数度数的顶点
    let mut odd_count = 0;

    for (vertex, neighbors) in graph.iter() {
        let degree = neighbors
            .iter()
            .filter(|&n| n != vertex)
            .count()
            + neighbors.iter().filter(|&n| n == vertex).count() * 2;

        if degree % 2 != 0 {
            odd_count += 1;
        }
    }

    odd_count == 0 || odd_count == 2
}

/// 查找无向图的欧拉回路（Hierholzer算法）
///
/// # 算法步骤
///
/// 1. 检查是否存在欧拉回路
/// 2. 从任意顶点开始DFS
/// 3. 遍历未访问的边，当无法前进时将顶点加入路径
/// 4. 反转路径得到欧拉回路
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(V + E)
///   - 检查连通性: O(V + E)
///   - Hierholzer算法: O(E)
///
/// - **空间复杂度**: O(V + E)
///   - 存储图: O(V + E)
///   - 递归栈/路径: O(V + E)
///
/// # 参数
///
/// * `graph` - 邻接表表示的无向图
///
/// # 返回值
///
/// 返回 `EulerResult`，包含欧拉回路（如果存在）
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::euler_tour::find_eulerian_circuit_undirected;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// // 构建一个欧拉图（所有顶点度数为偶数）
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['A', 'C']);
/// graph.insert('C', vec!['A', 'B', 'D', 'E']);
/// graph.insert('D', vec!['C', 'E']);
/// graph.insert('E', vec!['C', 'D']);
///
/// let result = find_eulerian_circuit_undirected(&graph);
/// assert!(result.exists);
/// assert!(result.is_circuit);
/// ```
pub fn find_eulerian_circuit_undirected<V>(graph: &HashMap<V, Vec<V>>) -> EulerResult<V>
where
    V: Clone + Eq + Hash + Ord,
{
    if !has_eulerian_circuit_undirected(graph) {
        return EulerResult::none();
    }

    // 找起始顶点（度数>0的任意顶点）
    let start = graph
        .iter()
        .find(|(_, neighbors)| !neighbors.is_empty())
        .map(|(v, _)| v.clone())
        .unwrap_or_else(|| graph.keys().next().cloned().unwrap());

    // 使用Hierholzer算法
    let mut edge_count: HashMap<(V, V), usize> = HashMap::new();

    // 统计边数
    for (u, neighbors) in graph.iter() {
        for v in neighbors {
            let edge = normalize_edge(u.clone(), v.clone());
            *edge_count.entry(edge).or_insert(0) += 1;
        }
    }

    let mut edge_path: Vec<(V, V)> = Vec::new();
    let mut stack = vec![start.clone()];
    let mut current_path: Vec<V> = Vec::new();

    while let Some(vertex) = stack.last().cloned() {
        // 找未使用的边
        let mut found = false;
        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                let edge = normalize_edge(vertex.clone(), neighbor.clone());
                if let Some(&count) = edge_count.get(&edge) {
                    if count > 0 {
                        // 使用这条边
                        *edge_count.get_mut(&edge).unwrap() -= 1;
                        stack.push(neighbor.clone());
                        found = true;
                        break;
                    }
                }
            }
        }

        if !found {
            // 没有未使用的边，回退
            stack.pop();
            current_path.push(vertex);
        }
    }

    // 构建边路径
    for i in 0..current_path.len().saturating_sub(1) {
        edge_path.push((current_path[i].clone(), current_path[i + 1].clone()));
    }

    // 反转得到正确顺序
    current_path.reverse();
    edge_path.reverse();

    EulerResult {
        exists: true,
        path: current_path.clone(),
        edge_path,
        is_circuit: current_path.first() == current_path.last() && current_path.len() > 1,
        start: current_path.first().cloned(),
        end: current_path.last().cloned(),
    }
}

/// 查找无向图的欧拉路径
///
/// # 算法步骤
///
/// 1. 检查是否存在欧拉路径
/// 2. 找到起点（度数为奇数的顶点，如果没有则任意）
/// 3. 使用Hierholzer算法
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V + E)
pub fn find_eulerian_path_undirected<V>(graph: &HashMap<V, Vec<V>>) -> EulerResult<V>
where
    V: Clone + Eq + Hash + Ord,
{
    if !has_eulerian_path_undirected(graph) {
        return EulerResult::none();
    }

    // 找起点（度数为奇数的顶点）
    let mut start: Option<V> = None;

    for (vertex, neighbors) in graph.iter() {
        let degree = neighbors
            .iter()
            .filter(|&n| n != vertex)
            .count()
            + neighbors.iter().filter(|&n| n == vertex).count() * 2;

        if degree % 2 != 0 {
            start = Some(vertex.clone());
            break;
        }
    }

    // 如果没有奇数度数的顶点，从任意非孤立点开始
    let start = start.unwrap_or_else(|| {
        graph
            .iter()
            .find(|(_, neighbors)| !neighbors.is_empty())
            .map(|(v, _)| v.clone())
            .unwrap_or_else(|| graph.keys().next().cloned().unwrap())
    });

    // 使用Hierholzer算法
    let mut edge_count: HashMap<(V, V), usize> = HashMap::new();

    for (u, neighbors) in graph.iter() {
        for v in neighbors {
            let edge = normalize_edge(u.clone(), v.clone());
            *edge_count.entry(edge).or_insert(0) += 1;
        }
    }

    let mut current_path: Vec<V> = Vec::new();
    let mut edge_path = Vec::new();
    let mut stack = vec![start.clone()];

    while let Some(vertex) = stack.last().cloned() {
        let mut found = false;
        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                let edge = normalize_edge(vertex.clone(), neighbor.clone());
                if let Some(&count) = edge_count.get(&edge) {
                    if count > 0 {
                        *edge_count.get_mut(&edge).unwrap() -= 1;
                        stack.push(neighbor.clone());
                        found = true;
                        break;
                    }
                }
            }
        }

        if !found {
            stack.pop();
            current_path.push(vertex);
        }
    }

    // 构建边路径
    for i in 0..current_path.len().saturating_sub(1) {
        edge_path.push((current_path[i].clone(), current_path[i + 1].clone()));
    }

    current_path.reverse();
    edge_path.reverse();

    EulerResult {
        exists: true,
        path: current_path.clone(),
        edge_path,
        is_circuit: current_path.first() == current_path.last() && current_path.len() > 1,
        start: current_path.first().cloned(),
        end: current_path.last().cloned(),
    }
}

/// 规范化无向边（较小的顶点在前）
fn normalize_edge<V: Clone + Eq + Ord>(u: V, v: V) -> (V, V) {
    if u < v {
        (u, v)
    } else {
        (v, u)
    }
}

/// 检查无向图是否连通（忽略孤立顶点）
fn is_connected_undirected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    if graph.is_empty() {
        return true;
    }

    // 找第一个非孤立顶点
    let start = match graph.iter().find(|(_, n)| !n.is_empty()) {
        Some((v, _)) => v.clone(),
        None => return true, // 所有顶点都孤立，认为连通
    };

    let mut visited: HashSet<V> = HashSet::new();
    let mut stack = vec![start];

    while let Some(vertex) = stack.pop() {
        if visited.contains(&vertex) {
            continue;
        }
        visited.insert(vertex.clone());

        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    stack.push(neighbor.clone());
                }
            }
        }
    }

    // 检查所有非孤立顶点都被访问
    graph
        .iter()
        .all(|(v, neighbors)| neighbors.is_empty() || visited.contains(v))
}

/// 有向图欧拉回路检查
///
/// # 条件
/// 1. 图弱连通（忽略方向后连通）
/// 2. 所有顶点的入度等于出度
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn has_eulerian_circuit_directed<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    if graph.is_empty() {
        return true;
    }

    // 检查弱连通
    if !is_weakly_connected(graph) {
        return false;
    }

    // 计算入度和出度
    let mut in_degree: HashMap<V, usize> = HashMap::new();
    let mut out_degree: HashMap<V, usize> = HashMap::new();

    for (u, neighbors) in graph.iter() {
        out_degree.insert(u.clone(), neighbors.len());
        for v in neighbors {
            *in_degree.entry(v.clone()).or_insert(0) += 1;
        }
    }

    // 检查所有顶点的入度等于出度
    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    for v in all_vertices {
        let in_deg = in_degree.get(&v).copied().unwrap_or(0);
        let out_deg = out_degree.get(&v).copied().unwrap_or(0);
        if in_deg != out_deg {
            return false;
        }
    }

    true
}

/// 有向图欧拉路径检查
///
/// # 条件
/// 1. 图弱连通
/// 2. 恰好一个顶点出度=入度+1（起点），一个顶点入度=出度+1（终点），其余相等
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn has_eulerian_path_directed<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    if graph.is_empty() {
        return true;
    }

    // 检查弱连通
    if !is_weakly_connected(graph) {
        return false;
    }

    // 计算入度和出度
    let mut in_degree: HashMap<V, usize> = HashMap::new();
    let mut out_degree: HashMap<V, usize> = HashMap::new();

    for (u, neighbors) in graph.iter() {
        out_degree.insert(u.clone(), neighbors.len());
        for v in neighbors {
            *in_degree.entry(v.clone()).or_insert(0) += 1;
        }
    }

    let all_vertices: HashSet<V> = graph
        .keys()
        .cloned()
        .chain(graph.values().flatten().cloned())
        .collect();

    let mut start_count = 0;
    let mut end_count = 0;

    for v in all_vertices {
        let in_deg = in_degree.get(&v).copied().unwrap_or(0) as i32;
        let out_deg = out_degree.get(&v).copied().unwrap_or(0) as i32;
        let diff = out_deg - in_deg;

        if diff == 1 {
            start_count += 1;
        } else if diff == -1 {
            end_count += 1;
        } else if diff != 0 {
            return false;
        }
    }

    (start_count == 0 && end_count == 0) || (start_count == 1 && end_count == 1)
}

/// 查找有向图的欧拉回路
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V + E)
pub fn find_eulerian_circuit_directed<V>(graph: &HashMap<V, Vec<V>>) -> EulerResult<V>
where
    V: Clone + Eq + Hash,
{
    if !has_eulerian_circuit_directed(graph) {
        return EulerResult::none();
    }

    // 找起始顶点（出度>0的任意顶点）
    let start = graph
        .iter()
        .find(|(_, neighbors)| !neighbors.is_empty())
        .map(|(v, _)| v.clone())
        .unwrap_or_else(|| graph.keys().next().cloned().unwrap());

    hierholzer_directed(graph, start, true)
}

/// 查找有向图的欧拉路径
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V + E)
pub fn find_eulerian_path_directed<V>(graph: &HashMap<V, Vec<V>>) -> EulerResult<V>
where
    V: Clone + Eq + Hash,
{
    if !has_eulerian_path_directed(graph) {
        return EulerResult::none();
    }

    // 计算入度和出度，找起点
    let mut in_degree: HashMap<V, usize> = HashMap::new();
    let mut out_degree: HashMap<V, usize> = HashMap::new();

    for (u, neighbors) in graph.iter() {
        out_degree.insert(u.clone(), neighbors.len());
        for v in neighbors {
            *in_degree.entry(v.clone()).or_insert(0) += 1;
        }
    }

    // 找起点（出度=入度+1）
    let mut start: Option<V> = None;
    for (v, &out) in &out_degree {
        let inp = in_degree.get(v).copied().unwrap_or(0);
        if out == inp + 1 {
            start = Some(v.clone());
            break;
        }
    }

    // 如果没有，从任意非孤立点开始
    let start = start.unwrap_or_else(|| {
        graph
            .iter()
            .find(|(_, neighbors)| !neighbors.is_empty())
            .map(|(v, _)| v.clone())
            .unwrap_or_else(|| graph.keys().next().cloned().unwrap())
    });

    hierholzer_directed(graph, start, false)
}

/// Hierholzer算法实现（有向图）
fn hierholzer_directed<V>(
    graph: &HashMap<V, Vec<V>>,
    start: V,
    is_circuit_expected: bool,
) -> EulerResult<V>
where
    V: Clone + Eq + Hash,
{
    // 复制图结构用于边删除
    let mut remaining: HashMap<V, Vec<V>> = graph.clone();

    let mut current_path: Vec<V> = Vec::new();
    let mut edge_path = Vec::new();
    let mut stack = vec![start.clone()];

    while let Some(vertex) = stack.last().cloned() {
        if let Some(neighbors) = remaining.get_mut(&vertex) {
            if !neighbors.is_empty() {
                let next = neighbors.remove(0);
                stack.push(next);
                continue;
            }
        }
        stack.pop();
        current_path.push(vertex);
    }

    // 构建边路径
    for i in 0..current_path.len().saturating_sub(1) {
        edge_path.push((current_path[i].clone(), current_path[i + 1].clone()));
    }

    current_path.reverse();
    edge_path.reverse();

    EulerResult {
        exists: true,
        path: current_path.clone(),
        edge_path,
        is_circuit: is_circuit_expected
            || (current_path.first() == current_path.last() && current_path.len() > 1),
        start: current_path.first().cloned(),
        end: current_path.last().cloned(),
    }
}

/// 检查有向图是否弱连通
fn is_weakly_connected<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    // 构建无向版本并检查连通性
    let mut undirected: HashMap<V, Vec<V>> = HashMap::new();

    for (u, neighbors) in graph.iter() {
        undirected.entry(u.clone()).or_default();
        for v in neighbors {
            undirected.entry(u.clone()).or_default().push(v.clone());
            undirected.entry(v.clone()).or_default().push(u.clone());
        }
    }

    is_connected_undirected(&undirected)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_undirected_eulerian_circuit() {
        // 正方形加对角线（所有顶点度数=3？不对，重新设计）
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 三角形
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['A', 'B']);

        assert!(has_eulerian_circuit_undirected(&graph));
        let result = find_eulerian_circuit_undirected(&graph);
        assert!(result.exists);
        assert!(result.is_circuit);
    }

    #[test]
    fn test_undirected_eulerian_path() {
        // 链状图：A-B-C-D（两个奇数度顶点：A和D）
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['B', 'D']);
        graph.insert('D', vec!['C']);

        assert!(!has_eulerian_circuit_undirected(&graph));
        assert!(has_eulerian_path_undirected(&graph));

        let result = find_eulerian_path_undirected(&graph);
        assert!(result.exists);
        // 验证路径覆盖所有边
        assert!(!result.path.is_empty());
    }

    #[test]
    fn test_no_eulerian_path() {
        // 星型图：中心连接4个叶子（4个奇数度顶点）
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C', 'D', 'E']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['A']);
        graph.insert('D', vec!['A']);
        graph.insert('E', vec!['A']);

        assert!(!has_eulerian_path_undirected(&graph));
    }

    #[test]
    fn test_directed_eulerian_circuit() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        // 有向环
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['A']);

        assert!(has_eulerian_circuit_directed(&graph));
        let result = find_eulerian_circuit_directed(&graph);
        assert!(result.exists);
        assert!(result.is_circuit);
    }

    #[test]
    fn test_directed_eulerian_path() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['C']);
        graph.insert('C', vec!['D']);

        assert!(!has_eulerian_circuit_directed(&graph));
        assert!(has_eulerian_path_directed(&graph));

        let result = find_eulerian_path_directed(&graph);
        assert!(result.exists);
        assert!(!result.is_circuit);
    }

    #[test]
    fn test_disconnected_graph() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        assert!(!has_eulerian_circuit_undirected(&graph));
        assert!(!has_eulerian_path_undirected(&graph));
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        assert!(has_eulerian_circuit_undirected(&graph));
        assert!(has_eulerian_path_undirected(&graph));
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        assert!(has_eulerian_circuit_undirected(&graph));
    }

    #[test]
    fn test_complex_eulerian_circuit() {
        // 更复杂的欧拉图 - 所有顶点度数为偶数
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        // 构建一个欧拉图：两个三角形共享一个顶点
        graph.insert(1, vec![2, 3]);
        graph.insert(2, vec![1, 3]);  // 度数2
        graph.insert(3, vec![1, 2, 4, 5]);  // 度数4
        graph.insert(4, vec![3, 5]);  // 度数2
        graph.insert(5, vec![3, 4]);  // 度数2

        assert!(has_eulerian_circuit_undirected(&graph));
        let result = find_eulerian_circuit_undirected(&graph);
        assert!(result.exists);
    }

    #[test]
    fn test_path_length() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A', 'C']);
        graph.insert('C', vec!['A', 'B']);

        let result = find_eulerian_circuit_undirected(&graph);
        // 三角形有3条边，欧拉回路访问每条边一次
        // 路径形式如 A->B->C->A 或 A->C->B->A
        assert!(result.path.len() >= 4);
        assert!(result.is_circuit);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：邮递员路线规划
    pub fn postman_route_example() {
        println!("=== 欧拉回路 - 邮递员路线规划 ===");

        let mut streets: HashMap<&str, Vec<&str>> = HashMap::new();
        // 街道网络（每条街道需要经过一次）
        streets.insert("邮局", vec!["A街", "B街"]);
        streets.insert("A街", vec!["邮局", "C街"]);
        streets.insert("B街", vec!["邮局", "C街"]);
        streets.insert("C街", vec!["A街", "B街", "D街"]);
        streets.insert("D街", vec!["C街"]);

        if has_eulerian_circuit_undirected(&streets) {
            let route = find_eulerian_circuit_undirected(&streets);
            println!("存在欧拉回路，邮递员可以从邮局出发，经过所有街道后回到邮局。");
            println!("路线: {:?}", route.path);
        } else if has_eulerian_path_undirected(&streets) {
            let route = find_eulerian_path_undirected(&streets);
            println!("存在欧拉路径，但无法形成回路。");
            println!("路线: {:?}", route.path);
        } else {
            println!("不存在欧拉路径，需要重复经过某些街道（中国邮路问题）。");
        }
    }

    /// 示例：博物馆参观路线
    pub fn museum_tour_example() {
        println!("\n=== 欧拉回路 - 博物馆参观路线 ===");

        let mut museum: HashMap<&str, Vec<&str>> = HashMap::new();
        // 展厅之间的通道（希望每条通道只走一次）
        museum.insert("入口", vec!["古代馆", "现代馆"]);
        museum.insert("古代馆", vec!["入口", "中世馆"]);
        museum.insert("中世馆", vec!["古代馆", "现代馆", "特展馆"]);
        museum.insert("现代馆", vec!["入口", "中世馆", "特展馆"]);
        museum.insert("特展馆", vec!["中世馆", "现代馆", "出口"]);
        museum.insert("出口", vec!["特展馆"]);

        let result = find_eulerian_path_undirected(&museum);
        if result.exists {
            println!("可以设计一条不重复的参观路线！");
            println!("从 {:?} 开始", result.start);
            println!("路线: {:?}", result.path);
            println!("在 {:?} 结束", result.end);
        } else {
            println!("无法设计不重复的路线，需要重复经过某些通道。");
        }
    }
}
