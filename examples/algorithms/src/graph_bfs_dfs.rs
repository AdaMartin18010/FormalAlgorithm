//! 图的广度优先搜索（BFS）和深度优先搜索（DFS）实现
//!
//! BFS和DFS是图遍历的基础算法，广泛应用于路径搜索、连通性检测等场景。

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

/// 图遍历结果
#[derive(Debug, Clone)]
pub struct GraphTraversalResult<V> {
    /// 遍历顺序
    pub order: Vec<V>,
    /// 访问的顶点集合
    pub visited: HashSet<V>,
    /// 父节点映射（用于重建路径）
    pub parents: HashMap<V, V>,
}

impl<V> GraphTraversalResult<V>
where
    V: Eq + Hash + Clone,
{
    /// 创建新的结果
    pub fn new() -> Self {
        GraphTraversalResult {
            order: Vec::new(),
            visited: HashSet::new(),
            parents: HashMap::new(),
        }
    }

    /// 重建从起点到目标点的路径
    pub fn path_to(&self, target: &V) -> Option<Vec<V>> {
        if !self.visited.contains(target) {
            return None;
        }

        let mut path = vec![target.clone()];
        let mut current = target.clone();

        while let Some(parent) = self.parents.get(&current) {
            path.push(parent.clone());
            current = parent.clone();
        }

        path.reverse();
        Some(path)
    }
}

impl<V> Default for GraphTraversalResult<V>
where
    V: Eq + Hash + Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

/// 广度优先搜索（BFS）
///
/// # 算法说明
///
/// BFS从起始顶点开始，逐层访问相邻顶点：
/// 1. 将起始顶点加入队列并标记为已访问
/// 2. 从队列中取出一个顶点
/// 3. 访问该顶点的所有未访问邻居，加入队列
/// 4. 重复步骤2-3直到队列为空
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V + E)
///   - V：顶点数
///   - E：边数
/// - **空间复杂度**：O(V)
///   - 队列和访问集合需要存储顶点
///
/// # 参数
///
/// * `graph` - 邻接表表示的图
/// * `start` - 起始顶点
///
/// # 返回值
///
/// 返回 `GraphTraversalResult`，包含遍历顺序和父节点信息
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::bfs;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['D', 'E']);
/// graph.insert('C', vec!['F']);
/// graph.insert('D', vec![]);
/// graph.insert('E', vec!['F']);
/// graph.insert('F', vec![]);
///
/// let result = bfs(&graph, 'A');
/// assert_eq!(result.order, vec!['A', 'B', 'C', 'D', 'E', 'F']);
/// ```
pub fn bfs<V>(graph: &HashMap<V, Vec<V>>, start: V) -> GraphTraversalResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut result = GraphTraversalResult::new();
    let mut queue = VecDeque::new();

    queue.push_back(start.clone());
    result.visited.insert(start.clone());
    result.order.push(start.clone());

    while let Some(vertex) = queue.pop_front() {
        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors {
                if !result.visited.contains(neighbor) {
                    result.visited.insert(neighbor.clone());
                    result.parents.insert(neighbor.clone(), vertex.clone());
                    result.order.push(neighbor.clone());
                    queue.push_back(neighbor.clone());
                }
            }
        }
    }

    result
}

/// 深度优先搜索（DFS）- 递归实现
///
/// # 算法说明
///
/// DFS从起始顶点开始，尽可能深地探索图的分支：
/// 1. 访问起始顶点并标记为已访问
/// 2. 递归访问所有未访问的邻居顶点
/// 3. 当没有未访问的邻居时，回溯
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V + E)
/// - **空间复杂度**：O(V) - 递归栈空间
///
/// # 参数
///
/// * `graph` - 邻接表表示的图
/// * `start` - 起始顶点
///
/// # 返回值
///
/// 返回 `GraphTraversalResult`，包含遍历顺序和父节点信息
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::dfs;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['D', 'E']);
/// graph.insert('C', vec!['F']);
/// graph.insert('D', vec![]);
/// graph.insert('E', vec!['F']);
/// graph.insert('F', vec![]);
///
/// let result = dfs(&graph, 'A');
/// assert_eq!(result.order[0], 'A');
/// assert!(result.visited.contains(&'F'));
/// ```
pub fn dfs<V>(graph: &HashMap<V, Vec<V>>, start: V) -> GraphTraversalResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut result = GraphTraversalResult::new();
    dfs_recursive(graph, start.clone(), &mut result);
    result
}

fn dfs_recursive<V>(graph: &HashMap<V, Vec<V>>, vertex: V, result: &mut GraphTraversalResult<V>)
where
    V: Clone + Eq + Hash,
{
    result.visited.insert(vertex.clone());
    result.order.push(vertex.clone());

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if !result.visited.contains(neighbor) {
                result.parents.insert(neighbor.clone(), vertex.clone());
                dfs_recursive(graph, neighbor.clone(), result);
            }
        }
    }
}

/// 深度优先搜索（DFS）- 迭代实现
///
/// 使用显式栈避免递归深度限制问题
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::dfs_iterative;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['D']);
/// graph.insert('C', vec![]);
/// graph.insert('D', vec![]);
///
/// let result = dfs_iterative(&graph, 'A');
/// assert_eq!(result.order[0], 'A');
/// ```
pub fn dfs_iterative<V>(graph: &HashMap<V, Vec<V>>, start: V) -> GraphTraversalResult<V>
where
    V: Clone + Eq + Hash,
{
    let mut result = GraphTraversalResult::new();
    let mut stack = vec![start.clone()];

    while let Some(vertex) = stack.pop() {
        if result.visited.contains(&vertex) {
            continue;
        }

        result.visited.insert(vertex.clone());
        result.order.push(vertex.clone());

        if let Some(neighbors) = graph.get(&vertex) {
            for neighbor in neighbors.iter().rev() {
                if !result.visited.contains(neighbor) {
                    result.parents.insert(neighbor.clone(), vertex.clone());
                    stack.push(neighbor.clone());
                }
            }
        }
    }

    result
}

/// 检测图中是否存在从起点到终点的路径
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::has_path;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['D']);
/// graph.insert('C', vec![]);
/// graph.insert('D', vec![]);
///
/// assert!(has_path(&graph, 'A', 'D'));
/// assert!(!has_path(&graph, 'D', 'A'));
/// ```
pub fn has_path<V>(graph: &HashMap<V, Vec<V>>, start: V, end: V) -> bool
where
    V: Clone + Eq + Hash,
{
    let result = bfs(graph, start);
    result.visited.contains(&end)
}

/// 查找图中所有连通分量
///
/// 返回每个连通分量的顶点集合
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::connected_components;
///
/// let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
/// graph.insert(1, vec![2]);
/// graph.insert(2, vec![1]);
/// graph.insert(3, vec![4]);
/// graph.insert(4, vec![3]);
/// graph.insert(5, vec![]);
///
/// let components = connected_components(&graph);
/// assert_eq!(components.len(), 3);
/// ```
pub fn connected_components<V>(graph: &HashMap<V, Vec<V>>) -> Vec<HashSet<V>>
where
    V: Clone + Eq + Hash,
{
    let mut visited = HashSet::new();
    let mut components = Vec::new();

    for vertex in graph.keys() {
        if !visited.contains(vertex) {
            let result = bfs(graph, vertex.clone());
            visited.extend(result.visited.iter().cloned());
            components.push(result.visited);
        }
    }

    components
}

/// 使用BFS查找最短路径（无权图）
///
/// 返回从起点到终点的最短路径
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::shortest_path;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['D', 'E']);
/// graph.insert('C', vec!['F']);
/// graph.insert('D', vec![]);
/// graph.insert('E', vec!['F']);
/// graph.insert('F', vec![]);
///
/// let path = shortest_path(&graph, 'A', 'F');
/// assert_eq!(path, Some(vec!['A', 'C', 'F']));
/// ```
pub fn shortest_path<V>(graph: &HashMap<V, Vec<V>>, start: V, end: V) -> Option<Vec<V>>
where
    V: Clone + Eq + Hash,
{
    if start == end {
        return Some(vec![start]);
    }

    let result = bfs(graph, start);
    result.path_to(&end)
}

/// 检测图中是否存在环（DFS实现）
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::has_cycle;
///
/// // 无环图
/// let mut dag: HashMap<char, Vec<char>> = HashMap::new();
/// dag.insert('A', vec!['B', 'C']);
/// dag.insert('B', vec!['D']);
/// dag.insert('C', vec![]);
/// dag.insert('D', vec![]);
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
    let mut white = HashSet::new(); // 未访问
    let mut gray = HashSet::new();  // 正在访问
    let mut black = HashSet::new(); // 已访问完成

    for vertex in graph.keys() {
        white.insert(vertex.clone());
    }

    while let Some(start) = white.iter().next().cloned() {
        if dfs_cycle_check(graph, start, &mut white, &mut gray, &mut black) {
            return true;
        }
    }

    false
}

fn dfs_cycle_check<V>(
    graph: &HashMap<V, Vec<V>>,
    vertex: V,
    white: &mut HashSet<V>,
    gray: &mut HashSet<V>,
    black: &mut HashSet<V>,
) -> bool
where
    V: Clone + Eq + Hash,
{
    white.remove(&vertex);
    gray.insert(vertex.clone());

    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if black.contains(neighbor) {
                continue;
            }
            if gray.contains(neighbor) {
                return true; // 发现回边，存在环
            }
            if dfs_cycle_check(graph, neighbor.clone(), white, gray, black) {
                return true;
            }
        }
    }

    gray.remove(&vertex);
    black.insert(vertex);
    false
}

/// 拓扑排序（Kahn算法）
///
/// 返回图的拓扑排序序列，如果图中有环则返回 None
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::graph_bfs_dfs::topological_sort;
///
/// let mut dag: HashMap<char, Vec<char>> = HashMap::new();
/// dag.insert('A', vec!['C']);
/// dag.insert('B', vec!['C', 'D']);
/// dag.insert('C', vec!['E']);
/// dag.insert('D', vec!['E']);
/// dag.insert('E', vec![]);
///
/// let sorted = topological_sort(&dag);
/// assert!(sorted.is_some());
/// let order = sorted.unwrap();
/// // A和B应该在C之前，C和D应该在E之前
/// assert!(order.iter().position(|&x| x == 'A').unwrap() < order.iter().position(|&x| x == 'C').unwrap());
/// assert!(order.iter().position(|&x| x == 'E').unwrap() > order.iter().position(|&x| x == 'C').unwrap());
/// ```
pub fn topological_sort<V>(graph: &HashMap<V, Vec<V>>) -> Option<Vec<V>>
where
    V: Clone + Eq + Hash,
{
    // 计算入度
    let mut in_degree: HashMap<V, usize> = HashMap::new();
    for (vertex, neighbors) in graph.iter() {
        in_degree.entry(vertex.clone()).or_insert(0);
        for neighbor in neighbors {
            *in_degree.entry(neighbor.clone()).or_insert(0) += 1;
        }
    }

    // 将所有入度为0的顶点加入队列
    let mut queue = VecDeque::new();
    for (vertex, &degree) in in_degree.iter() {
        if degree == 0 {
            queue.push_back(vertex.clone());
        }
    }

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

    // 如果结果中顶点数少于图中顶点数，说明有环
    if result.len() == in_degree.len() {
        Some(result)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_graph() -> HashMap<char, Vec<char>> {
        let mut graph = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['D', 'E']);
        graph.insert('C', vec!['F']);
        graph.insert('D', vec![]);
        graph.insert('E', vec!['F']);
        graph.insert('F', vec![]);
        graph
    }

    #[test]
    fn test_bfs_basic() {
        let graph = create_test_graph();
        let result = bfs(&graph, 'A');

        assert_eq!(result.order[0], 'A');
        assert!(result.visited.contains(&'F'));
        assert_eq!(result.visited.len(), 6);
    }

    #[test]
    fn test_dfs_basic() {
        let graph = create_test_graph();
        let result = dfs(&graph, 'A');

        assert_eq!(result.order[0], 'A');
        assert!(result.visited.contains(&'F'));
        assert_eq!(result.visited.len(), 6);
    }

    #[test]
    fn test_dfs_iterative() {
        let graph = create_test_graph();
        let result = dfs_iterative(&graph, 'A');

        assert_eq!(result.order[0], 'A');
        assert!(result.visited.contains(&'F'));
        assert_eq!(result.visited.len(), 6);
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = bfs(&graph, 'A');

        assert_eq!(result.order, vec!['A']);
        assert_eq!(result.visited.len(), 1);
    }

    #[test]
    fn test_single_vertex() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec![]);

        let result = bfs(&graph, 'A');
        assert_eq!(result.order, vec!['A']);
    }

    #[test]
    fn test_has_path() {
        let graph = create_test_graph();

        assert!(has_path(&graph, 'A', 'F'));
        assert!(has_path(&graph, 'B', 'F'));
        assert!(!has_path(&graph, 'F', 'A'));
        assert!(!has_path(&graph, 'D', 'E'));
    }

    #[test]
    fn test_shortest_path() {
        let graph = create_test_graph();

        let path = shortest_path(&graph, 'A', 'F');
        assert_eq!(path, Some(vec!['A', 'C', 'F']));

        let path = shortest_path(&graph, 'A', 'D');
        assert_eq!(path, Some(vec!['A', 'B', 'D']));

        let path = shortest_path(&graph, 'D', 'A');
        assert_eq!(path, None);
    }

    #[test]
    fn test_connected_components() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2]);
        graph.insert(2, vec![1, 3]);
        graph.insert(3, vec![2]);
        graph.insert(4, vec![5]);
        graph.insert(5, vec![4]);
        graph.insert(6, vec![]);

        let components = connected_components(&graph);
        assert_eq!(components.len(), 3);
    }

    #[test]
    fn test_has_cycle() {
        // 无环图
        let mut dag: HashMap<char, Vec<char>> = HashMap::new();
        dag.insert('A', vec!['B', 'C']);
        dag.insert('B', vec!['D']);
        dag.insert('C', vec![]);
        dag.insert('D', vec![]);
        assert!(!has_cycle(&dag));

        // 有环图
        let mut cyclic: HashMap<char, Vec<char>> = HashMap::new();
        cyclic.insert('A', vec!['B']);
        cyclic.insert('B', vec!['C']);
        cyclic.insert('C', vec!['A']);
        assert!(has_cycle(&cyclic));

        // 自环
        let mut self_loop: HashMap<char, Vec<char>> = HashMap::new();
        self_loop.insert('A', vec!['A']);
        assert!(has_cycle(&self_loop));
    }

    #[test]
    fn test_topological_sort() {
        let mut dag: HashMap<char, Vec<char>> = HashMap::new();
        dag.insert('A', vec!['C']);
        dag.insert('B', vec!['C', 'D']);
        dag.insert('C', vec!['E']);
        dag.insert('D', vec!['E']);
        dag.insert('E', vec![]);

        let sorted = topological_sort(&dag);
        assert!(sorted.is_some());
        let order = sorted.unwrap();

        // 验证拓扑序
        let pos = |c| order.iter().position(|&x| x == c).unwrap();
        assert!(pos('A') < pos('C'));
        assert!(pos('B') < pos('C'));
        assert!(pos('B') < pos('D'));
        assert!(pos('C') < pos('E'));
        assert!(pos('D') < pos('E'));
    }

    #[test]
    fn test_topological_sort_cycle() {
        let mut cyclic: HashMap<char, Vec<char>> = HashMap::new();
        cyclic.insert('A', vec!['B']);
        cyclic.insert('B', vec!['C']);
        cyclic.insert('C', vec!['A']);

        let sorted = topological_sort(&cyclic);
        assert!(sorted.is_none());
    }

    #[test]
    fn test_bfs_with_numbers() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![2, 3]);
        graph.insert(2, vec![4, 5]);
        graph.insert(3, vec![6]);
        graph.insert(4, vec![]);
        graph.insert(5, vec![6]);
        graph.insert(6, vec![]);

        let result = bfs(&graph, 1);
        assert_eq!(result.order[0], 1);
        assert!(result.visited.contains(&6));
    }

    #[test]
    fn test_disconnected_graph_bfs() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['D']);
        graph.insert('D', vec!['C']);

        let result = bfs(&graph, 'A');
        assert!(result.visited.contains(&'A'));
        assert!(result.visited.contains(&'B'));
        assert!(!result.visited.contains(&'C'));
        assert!(!result.visited.contains(&'D'));
    }
}
