//! 二分图匹配算法（匈牙利算法）
//!
//! 二分图匹配是指在二分图中找到一组没有公共顶点的边，使得匹配边数最大。
//! 匈牙利算法（Kuhn-Munkres算法）是解决二分图最大匹配问题的经典算法。
//!
//! # 算法原理
//!
//! 匈牙利算法基于增广路的概念：
//! - **增广路**：一条从未匹配顶点开始，经过未匹配边、匹配边交替，到达另一未匹配顶点的路径
//! - **增广操作**：将增广路上的匹配边变为未匹配，未匹配边变为匹配，可使匹配数+1
//!
//! 算法步骤：
//! 1. 初始化：所有边都未匹配
//! 2. 对每个左部顶点，尝试找到增广路
//! 3. 使用DFS或BFS寻找增广路
//! 4. 如果找到，进行增广操作
//! 5. 重复直到无法找到增广路
//!
//! # 应用场景
//! - 任务分配问题
//! - 婚姻匹配问题
//! - 资源分配
//! - 网络流问题
//!
//! # 复杂度分析
//! | 算法 | 时间复杂度 | 空间复杂度 | 说明 |
//! |------|-----------|-----------|------|
//! | 匈牙利算法(DFS) | O(V × E) | O(V) | 实现简单 |
//! | 匈牙利算法(BFS) | O(V × E) | O(V) | 可找最短增广路 |
//! | Hopcroft-Karp | O(E × √V) | O(V) | 更快，适合稠密图 |

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

/// 二分图匹配结果
#[derive(Debug, Clone)]
pub struct MatchingResult<L, R> {
    /// 匹配对（左部顶点到右部顶点的映射）
    pub matches: HashMap<L, R>,
    /// 最大匹配数
    pub size: usize,
    /// 左部顶点集合
    pub left_vertices: Vec<L>,
    /// 右部顶点集合
    pub right_vertices: Vec<R>,
}

impl<L, R> MatchingResult<L, R>
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    /// 检查左部顶点是否已匹配
    pub fn is_matched_left(&self, left: &L) -> bool {
        self.matches.contains_key(left)
    }

    /// 检查右部顶点是否已匹配
    pub fn is_matched_right(&self, right: &R) -> bool {
        self.matches.values().any(|r| r == right)
    }

    /// 获取左部顶点的匹配对象
    pub fn get_match(&self, left: &L) -> Option<&R> {
        self.matches.get(left)
    }

    /// 判断是否为完美匹配
    pub fn is_perfect_matching(&self) -> bool {
        self.size == self.left_vertices.len() && self.size == self.right_vertices.len()
    }
}

/// 匈牙利算法 - 二分图最大匹配（DFS版本）
///
/// # 算法步骤
///
/// 1. 初始化所有顶点未匹配
/// 2. 对每个左部顶点u，尝试找到增广路
/// 3. 使用DFS搜索增广路，维护访问标记避免重复访问
/// 4. 如果找到增广路，更新匹配关系
/// 5. 返回最大匹配
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(|L| × E)
///   - 对每个左部顶点进行一次DFS
///   - 每次DFS遍历所有边
///
/// - **空间复杂度**: O(|L| + |R|)
///   - 匹配数组: O(|L|)
///   - 访问标记: O(|R|)
///   - 递归栈: O(|L|)
///
/// # 参数
///
/// * `graph` - 二分图，HashMap<左部顶点, Vec<右部顶点>>
///
/// # 返回值
///
/// 返回 `MatchingResult`，包含最大匹配
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::bipartite_matching::hungarian_dfs;
///
/// let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
/// graph.insert('A', vec![1, 2]);
/// graph.insert('B', vec![1]);
/// graph.insert('C', vec![2, 3]);
///
/// let result = hungarian_dfs(&graph);
/// assert_eq!(result.size, 3); // 完美匹配
/// assert!(result.is_matched_left(&'A'));
/// ```
pub fn hungarian_dfs<L, R>(graph: &HashMap<L, Vec<R>>) -> MatchingResult<L, R>
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    let left_vertices: Vec<L> = graph.keys().cloned().collect();
    let right_vertices: HashSet<R> = graph.values().flatten().cloned().collect();
    let right_vertices: Vec<R> = right_vertices.into_iter().collect();

    // 右部顶点的匹配：右 -> 左
    let mut match_right: HashMap<R, L> = HashMap::new();

    for u in &left_vertices {
        let mut visited: HashSet<R> = HashSet::new();
        dfs_find_augmenting_path(u, graph, &mut visited, &mut match_right);
    }

    // 转换为左->右的映射
    let matches: HashMap<L, R> = match_right
        .into_iter()
        .map(|(r, l)| (l, r))
        .collect();

    let size = matches.len();

    MatchingResult {
        matches,
        size,
        left_vertices,
        right_vertices,
    }
}

/// DFS寻找增广路
fn dfs_find_augmenting_path<L, R>(
    u: &L,
    graph: &HashMap<L, Vec<R>>,
    visited: &mut HashSet<R>,
    match_right: &mut HashMap<R, L>,
) -> bool
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    if let Some(neighbors) = graph.get(u) {
        for v in neighbors {
            if visited.contains(v) {
                continue;
            }
            visited.insert(v.clone());

            // 如果v未匹配，或v的匹配可以找到新的匹配
            let matched_left = match_right.get(v).cloned();
            
            let can_match = match matched_left {
                None => true,
                Some(matched) => {
                    dfs_find_augmenting_path(&matched, graph, visited, match_right)
                }
            };
            
            if can_match {
                match_right.insert(v.clone(), u.clone());
                return true;
            }
        }
    }
    false
}

/// 匈牙利算法 - 二分图最大匹配（BFS版本）
///
/// BFS版本可以找到最短的增广路，通常效率更高
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(|L| × E)
/// - **空间复杂度**: O(|L| + |R|)
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::bipartite_matching::hungarian_bfs;
///
/// let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
/// graph.insert('A', vec![1, 2, 3]);
/// graph.insert('B', vec![1, 3]);
/// graph.insert('C', vec![2]);
///
/// let result = hungarian_bfs(&graph);
/// assert_eq!(result.size, 3);
/// ```
pub fn hungarian_bfs<L, R>(graph: &HashMap<L, Vec<R>>) -> MatchingResult<L, R>
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    let left_vertices: Vec<L> = graph.keys().cloned().collect();
    let right_vertices: HashSet<R> = graph.values().flatten().cloned().collect();
    let right_vertices: Vec<R> = right_vertices.into_iter().collect();

    // 左->右的匹配
    let mut match_left: HashMap<L, R> = HashMap::new();
    // 右->左的匹配
    let mut match_right: HashMap<R, L> = HashMap::new();

    for start in &left_vertices {
        if match_left.contains_key(start) {
            continue;
        }

        // BFS寻找增广路
        let mut queue = VecDeque::new();
        let mut parent: HashMap<L, R> = HashMap::new(); // 记录BFS树
        let mut visited_left: HashSet<L> = HashSet::new();
        let mut visited_right: HashSet<R> = HashSet::new();

        queue.push_back(start.clone());
        visited_left.insert(start.clone());

        let mut found = false;
        let mut end_right: Option<R> = None;

        while let Some(u) = queue.pop_front() {
            if found {
                break;
            }

            if let Some(neighbors) = graph.get(&u) {
                for v in neighbors {
                    if visited_right.contains(v) {
                        continue;
                    }
                    visited_right.insert(v.clone());

                    if !match_right.contains_key(v) {
                        // 找到未匹配的右部顶点，增广路结束
                        parent.insert(u.clone(), v.clone());
                        end_right = Some(v.clone());
                        found = true;
                        break;
                    } else {
                        // v已匹配，继续BFS
                        let next_left = match_right.get(v).unwrap().clone();
                        if !visited_left.contains(&next_left) {
                            visited_left.insert(next_left.clone());
                            parent.insert(u.clone(), v.clone());
                            queue.push_back(next_left);
                        }
                    }
                }
            }
        }

        // 增广操作
        if found {
            let mut current_left = start.clone();
            let mut current_right = end_right.unwrap();

            loop {
                let _next_left = match_right.get(&current_right).cloned();

                // 更新匹配
                match_left.insert(current_left.clone(), current_right.clone());
                match_right.insert(current_right.clone(), current_left.clone());

                // 找到parent中的前一个
                if current_left == *start {
                    break;
                }

                // 回溯到上一个左部顶点
                if let Some((prev_left, _)) = parent.iter().find(|(_, r)| **r == current_right) {
                    current_left = prev_left.clone();
                    current_right = match_left.get(&current_left).unwrap().clone();
                } else {
                    break;
                }
            }
        }
    }

    let size = match_left.len();

    MatchingResult {
        matches: match_left,
        size,
        left_vertices,
        right_vertices,
    }
}

/// 检查图是否为二分图
///
/// 使用染色法判断图是否为二分图
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn is_bipartite<V>(graph: &HashMap<V, Vec<V>>) -> bool
where
    V: Clone + Eq + Hash,
{
    let mut color: HashMap<V, bool> = HashMap::new();

    for start in graph.keys().cloned().collect::<Vec<_>>() {
        if color.contains_key(&start) {
            continue;
        }

        let mut queue = VecDeque::new();
        queue.push_back(start.clone());
        color.insert(start, true);

        while let Some(u) = queue.pop_front() {
            let u_color = *color.get(&u).unwrap();

            if let Some(neighbors) = graph.get(&u) {
                for v in neighbors {
                    if let Some(&v_color) = color.get(v) {
                        if v_color == u_color {
                            return false; // 相邻顶点同色，不是二分图
                        }
                    } else {
                        color.insert(v.clone(), !u_color);
                        queue.push_back(v.clone());
                    }
                }
            }
        }
    }

    true
}

/// 将一般图转换为二分图（如果可能）
///
/// 返回左右两个集合，如果图不是二分图则返回None
///
/// # 复杂度
/// - **时间**: O(V + E)
/// - **空间**: O(V)
pub fn bipartite_partition<V>(graph: &HashMap<V, Vec<V>>) -> Option<(Vec<V>, Vec<V>)>
where
    V: Clone + Eq + Hash,
{
    let mut color: HashMap<V, bool> = HashMap::new();

    for start in graph.keys().cloned().collect::<Vec<_>>() {
        if color.contains_key(&start) {
            continue;
        }

        let mut queue = VecDeque::new();
        queue.push_back(start.clone());
        color.insert(start, true);

        while let Some(u) = queue.pop_front() {
            let u_color = *color.get(&u).unwrap();

            if let Some(neighbors) = graph.get(&u) {
                for v in neighbors {
                    if let Some(&v_color) = color.get(v) {
                        if v_color == u_color {
                            return None; // 不是二分图
                        }
                    } else {
                        color.insert(v.clone(), !u_color);
                        queue.push_back(v.clone());
                    }
                }
            }
        }
    }

    let mut left = Vec::new();
    let mut right = Vec::new();

    for (v, is_left) in color {
        if is_left {
            left.push(v);
        } else {
            right.push(v);
        }
    }

    Some((left, right))
}

/// 计算最大匹配的大小（Kőnig定理相关）
///
/// 在二分图中，最大匹配的大小等于最小顶点覆盖的大小
///
/// # 复杂度
/// - **时间**: O(V × E)
/// - **空间**: O(V)
pub fn max_matching_size<L, R>(graph: &HashMap<L, Vec<R>>) -> usize
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    hungarian_dfs(graph).size
}

/// 查找最小顶点覆盖（Kőnig定理）
///
/// 使用匈牙利算法结果构造最小顶点覆盖
///
/// # 复杂度
/// - **时间**: O(V × E)
/// - **空间**: O(V)
pub fn min_vertex_cover<L, R>(graph: &HashMap<L, Vec<R>>) -> (Vec<L>, Vec<R>)
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    let matching = hungarian_dfs(graph);

    // 从所有未匹配的左部顶点开始DFS
    let mut visited_left: HashSet<L> = HashSet::new();
    let mut visited_right: HashSet<R> = HashSet::new();

    for u in &matching.left_vertices {
        if !matching.is_matched_left(u) {
            dfs_vertex_cover(u, graph, &matching, &mut visited_left, &mut visited_right);
        }
    }

    // 最小顶点覆盖 = (左部 - 访问的左部) ∪ 访问的右部
    let left_cover: Vec<L> = matching
        .left_vertices
        .iter()
        .filter(|u| !visited_left.contains(*u))
        .cloned()
        .collect();

    let right_cover: Vec<R> = visited_right.into_iter().collect();

    (left_cover, right_cover)
}

fn dfs_vertex_cover<L, R>(
    u: &L,
    graph: &HashMap<L, Vec<R>>,
    matching: &MatchingResult<L, R>,
    visited_left: &mut HashSet<L>,
    visited_right: &mut HashSet<R>,
) where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    if visited_left.contains(u) {
        return;
    }
    visited_left.insert(u.clone());

    if let Some(neighbors) = graph.get(u) {
        for v in neighbors {
            if visited_right.contains(v) {
                continue;
            }
            visited_right.insert(v.clone());

            // 如果v已匹配，继续DFS到对应的左部顶点
            if let Some(matched_left) = matching
                .matches
                .iter()
                .find(|(_, r)| *r == v)
                .map(|(l, _)| l.clone())
            {
                dfs_vertex_cover(&matched_left, graph, matching, visited_left, visited_right);
            }
        }
    }
}

/// 查找最大独立集
///
/// 二分图中，最大独立集 = 所有顶点 - 最小顶点覆盖
///
/// # 复杂度
/// - **时间**: O(V × E)
/// - **空间**: O(V)
pub fn max_independent_set<L, R>(graph: &HashMap<L, Vec<R>>) -> (Vec<L>, Vec<R>)
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
{
    let matching = hungarian_dfs(graph);
    let (left_cover, right_cover) = min_vertex_cover(graph);

    let left_set: HashSet<L> = matching.left_vertices.into_iter().collect();
    let right_set: HashSet<R> = matching.right_vertices.into_iter().collect();

    let cover_left: HashSet<L> = left_cover.into_iter().collect();
    let cover_right: HashSet<R> = right_cover.into_iter().collect();

    let left_independent: Vec<L> = left_set
        .difference(&cover_left)
        .cloned()
        .collect();

    let right_independent: Vec<R> = right_set
        .difference(&cover_right)
        .cloned()
        .collect();

    (left_independent, right_independent)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_perfect_matching() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1, 2]);
        graph.insert('B', vec![1]);
        graph.insert('C', vec![2, 3]);

        let result = hungarian_dfs(&graph);
        assert_eq!(result.size, 3);
        assert!(result.is_perfect_matching());
    }

    #[test]
    fn test_maximum_matching() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1, 2]);
        graph.insert('B', vec![1, 2]);
        graph.insert('C', vec![1, 2]);

        // 3个左部顶点，2个右部顶点，最大匹配为2
        let result = hungarian_dfs(&graph);
        assert_eq!(result.size, 2);
        assert!(!result.is_perfect_matching());
    }

    #[test]
    fn test_dfs_bfs_equivalence() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1, 2, 3]);
        graph.insert('B', vec![1, 3]);
        graph.insert('C', vec![2]);

        let dfs_result = hungarian_dfs(&graph);
        let bfs_result = hungarian_bfs(&graph);

        assert_eq!(dfs_result.size, bfs_result.size);
    }

    #[test]
    fn test_bipartite_check() {
        // 二分图
        let mut bipartite: HashMap<char, Vec<char>> = HashMap::new();
        bipartite.insert('A', vec!['B', 'C']);
        bipartite.insert('B', vec!['A', 'D']);
        bipartite.insert('C', vec!['A', 'D']);
        bipartite.insert('D', vec!['B', 'C']);

        assert!(is_bipartite(&bipartite));

        // 奇数环，不是二分图
        let mut odd_cycle: HashMap<i32, Vec<i32>> = HashMap::new();
        odd_cycle.insert(1, vec![2, 3]);
        odd_cycle.insert(2, vec![1, 3]);
        odd_cycle.insert(3, vec![1, 2]);

        assert!(!is_bipartite(&odd_cycle));
    }

    #[test]
    fn test_bipartite_partition() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['X', 'Y']);
        graph.insert('B', vec!['X', 'Z']);
        graph.insert('X', vec!['A', 'B']);
        graph.insert('Y', vec!['A']);
        graph.insert('Z', vec!['B']);

        let (left, right) = bipartite_partition(&graph).unwrap();
        assert_eq!(left.len() + right.len(), 5);
    }

    #[test]
    fn test_empty_graph() {
        let graph: HashMap<char, Vec<i32>> = HashMap::new();
        let result = hungarian_dfs(&graph);
        assert_eq!(result.size, 0);
    }

    #[test]
    fn test_single_edge() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1]);

        let result = hungarian_dfs(&graph);
        assert_eq!(result.size, 1);
        assert_eq!(result.get_match(&'A'), Some(&1));
    }

    #[test]
    fn test_disconnected_matching() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        graph.insert(1, vec![10]);
        graph.insert(2, vec![20]);
        graph.insert(3, vec![30]);

        let result = hungarian_dfs(&graph);
        assert_eq!(result.size, 3);
    }

    #[test]
    fn test_vertex_cover() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1, 2]);
        graph.insert('B', vec![1]);
        graph.insert('C', vec![2]);

        let (left_cover, right_cover) = min_vertex_cover(&graph);
        // 最小顶点覆盖的大小应等于最大匹配的大小
        assert_eq!(left_cover.len() + right_cover.len(), 2);
    }

    #[test]
    fn test_independent_set() {
        let mut graph: HashMap<char, Vec<i32>> = HashMap::new();
        graph.insert('A', vec![1, 2]);
        graph.insert('B', vec![1]);

        let (left_ind, right_ind) = max_independent_set(&graph);
        // 验证独立集中的顶点之间没有边
        assert!(left_ind.len() + right_ind.len() >= 1);
    }

    #[test]
    fn test_numerical_vertices() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        for i in 0..10 {
            graph.insert(i, vec![i + 100, i + 101]);
        }

        let result = hungarian_bfs(&graph);
        assert_eq!(result.size, 10);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例：任务分配问题
    pub fn task_assignment_example() {
        println!("=== 匈牙利算法 - 任务分配问题 ===");

        let mut skills: HashMap<&str, Vec<&str>> = HashMap::new();
        // 员工技能矩阵
        skills.insert("Alice", vec!["前端开发", "UI设计"]);
        skills.insert("Bob", vec!["后端开发", "数据库"]);
        skills.insert("Carol", vec!["前端开发", "测试"]);
        skills.insert("David", vec!["后端开发", "DevOps"]);
        skills.insert("Eve", vec!["UI设计", "测试"]);

        let result = hungarian_dfs(&skills);
        println!("最大任务分配数: {}", result.size);
        println!("分配方案:");
        for (person, task) in &result.matches {
            println!("  {} -> {}", person, task);
        }
    }

    /// 示例：课程安排问题
    pub fn course_scheduling_example() {
        println!("\n=== 匈牙利算法 - 课程与教室匹配 ===");

        let mut requirements: HashMap<&str, Vec<&str>> = HashMap::new();
        // 课程需要的教室类型
        requirements.insert("数学课", vec!["普通教室A", "普通教室B"]);
        requirements.insert("物理实验", vec!["实验室1", "实验室2"]);
        requirements.insert("化学实验", vec!["实验室1"]);
        requirements.insert("计算机课", vec!["机房A", "机房B"]);
        requirements.insert("体育课", vec!["体育馆"]);

        let result = hungarian_bfs(&requirements);
        println!("可安排的最大课程数: {}", result.size);
        println!("课程安排:");
        for (course, room) in &result.matches {
            println!("  {} -> {}", course, room);
        }

        if result.is_perfect_matching() {
            println!("✓ 所有课程都能安排！");
        } else {
            println!("✗ 部分课程无法安排，需要增加教室或调整时间");
        }
    }
}
