//! 回溯算法框架与实现
//!
//! 回溯算法通过系统地搜索解空间来求解问题。
//! 本模块包含：子集和问题、图着色问题、全排列生成。

use std::collections::HashMap;

/// 子集和问题结果
#[derive(Debug, Clone, PartialEq)]
pub struct SubsetSumResult {
    /// 是否找到解
    pub found: bool,
    /// 解的子集（元素索引）
    pub indices: Vec<usize>,
    /// 解的子集（元素值）
    pub values: Vec<i64>,
}

/// 子集和问题
///
/// 给定一个正整数集合，判断是否存在一个子集，其和等于目标值
///
/// # 算法说明
///
/// 使用回溯法枚举所有可能的子集：
/// 1. 对每个元素，选择包含或不包含
/// 2. 剪枝：当前和超过目标值时停止递归
/// 3. 找到解时立即返回
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(2^n) 最坏情况
/// - **空间复杂度**：O(n) 递归栈
///
/// # 参数
///
/// * `nums` - 正整数集合
/// * `target` - 目标和
///
/// # 返回值
///
/// 返回 `SubsetSumResult`，包含是否找到解和解的子集
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking::subset_sum;
///
/// let nums = vec![3, 34, 4, 12, 5, 2];
/// let result = subset_sum(&nums, 9);
///
/// assert!(result.found);
/// assert_eq!(result.values.iter().sum::<i64>(), 9);
/// ```
pub fn subset_sum(nums: &[i64], target: i64) -> SubsetSumResult {
    let mut indices = Vec::new();
    let mut values = Vec::new();

    if subset_sum_backtrack(nums, target, 0, &mut indices, &mut values) {
        SubsetSumResult {
            found: true,
            indices,
            values,
        }
    } else {
        SubsetSumResult {
            found: false,
            indices: vec![],
            values: vec![],
        }
    }
}

fn subset_sum_backtrack(
    nums: &[i64],
    remaining: i64,
    start: usize,
    indices: &mut Vec<usize>,
    values: &mut Vec<i64>,
) -> bool {
    // 基本情况：找到解
    if remaining == 0 {
        return true;
    }

    // 剪枝：不可能有解
    if remaining < 0 || start >= nums.len() {
        return false;
    }

    // 尝试包含当前元素
    indices.push(start);
    values.push(nums[start]);
    if subset_sum_backtrack(nums, remaining - nums[start], start + 1, indices, values) {
        return true;
    }
    indices.pop();
    values.pop();

    // 尝试不包含当前元素
    if subset_sum_backtrack(nums, remaining, start + 1, indices, values) {
        return true;
    }

    false
}

/// 图着色结果
#[derive(Debug, Clone, PartialEq)]
pub struct GraphColoringResult {
    /// 是否可着色
    pub colorable: bool,
    /// 每个顶点的颜色（0表示未着色）
    pub colors: HashMap<char, usize>,
    /// 使用的颜色数
    pub num_colors: usize,
}

/// 图着色问题
///
/// 给定一个图和颜色数m，判断是否能用m种颜色给图的顶点着色，
/// 使得相邻顶点颜色不同
///
/// # 算法说明
///
/// 使用回溯法尝试给每个顶点着色：
/// 1. 选择一个顶点
/// 2. 尝试每种颜色
/// 3. 如果颜色与邻居不冲突，递归处理下一个顶点
/// 4. 如果无法着色，回溯
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m^n)，m是颜色数，n是顶点数
/// - **空间复杂度**：O(n)
///
/// # 参数
///
/// * `graph` - 邻接表表示的图
/// * `num_colors` - 可用颜色数
///
/// # 返回值
///
/// 返回 `GraphColoringResult`，包含着色方案和使用的颜色数
///
/// # 示例
///
/// ```
/// use std::collections::HashMap;
/// use formal_algorithms::backtracking::graph_coloring;
///
/// let mut graph: HashMap<char, Vec<char>> = HashMap::new();
/// graph.insert('A', vec!['B', 'C']);
/// graph.insert('B', vec!['A', 'C', 'D']);
/// graph.insert('C', vec!['A', 'B', 'D']);
/// graph.insert('D', vec!['B', 'C']);
///
/// let result = graph_coloring(&graph, 3);
/// assert!(result.colorable);
/// assert_eq!(result.num_colors, 3);
/// ```
pub fn graph_coloring(graph: &HashMap<char, Vec<char>>, num_colors: usize) -> GraphColoringResult {
    let vertices: Vec<char> = graph.keys().cloned().collect();
    let mut colors: HashMap<char, usize> = HashMap::new();

    if graph_coloring_backtrack(graph, &vertices, 0, num_colors, &mut colors) {
        let used_colors = colors.values().cloned().max().unwrap_or(0);
        GraphColoringResult {
            colorable: true,
            colors,
            num_colors: used_colors,
        }
    } else {
        GraphColoringResult {
            colorable: false,
            colors: HashMap::new(),
            num_colors: 0,
        }
    }
}

fn graph_coloring_backtrack(
    graph: &HashMap<char, Vec<char>>,
    vertices: &[char],
    index: usize,
    num_colors: usize,
    colors: &mut HashMap<char, usize>,
) -> bool {
    // 所有顶点都已着色
    if index == vertices.len() {
        return true;
    }

    let vertex = vertices[index];

    // 尝试每种颜色
    for color in 1..=num_colors {
        if is_safe_color(graph, vertex, color, colors) {
            colors.insert(vertex, color);

            if graph_coloring_backtrack(graph, vertices, index + 1, num_colors, colors) {
                return true;
            }

            colors.remove(&vertex); // 回溯
        }
    }

    false
}

/// 检查颜色是否安全（不与邻居冲突）
fn is_safe_color(
    graph: &HashMap<char, Vec<char>>,
    vertex: char,
    color: usize,
    colors: &HashMap<char, usize>,
) -> bool {
    if let Some(neighbors) = graph.get(&vertex) {
        for neighbor in neighbors {
            if let Some(&neighbor_color) = colors.get(neighbor) {
                if neighbor_color == color {
                    return false;
                }
            }
        }
    }
    true
}

/// 全排列结果
pub type PermutationsResult<T> = Vec<Vec<T>>;

/// 生成全排列
///
/// 给定一个序列，生成所有可能的排列
///
/// # 算法说明
///
/// 使用回溯法生成排列：
/// 1. 固定第一个位置，递归生成剩余元素的排列
/// 2. 交换元素来尝试不同的首元素
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n!)
/// - **空间复杂度**：O(n) 递归栈
///
/// # 参数
///
/// * `nums` - 输入序列
///
/// # 返回值
///
/// 返回所有排列的列表
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking::generate_permutations;
///
/// let nums = vec![1, 2, 3];
/// let perms = generate_permutations(&nums);
///
/// assert_eq!(perms.len(), 6);
/// assert!(perms.contains(&vec![1, 2, 3]));
/// assert!(perms.contains(&vec![3, 2, 1]));
/// ```
pub fn generate_permutations<T: Clone + Eq>(nums: &[T]) -> PermutationsResult<T> {
    let mut result = Vec::new();
    let mut current = nums.to_vec();

    permute_backtrack(&mut current, 0, &mut result);

    result
}

fn permute_backtrack<T: Clone + Eq>(nums: &mut [T], start: usize, result: &mut Vec<Vec<T>>) {
    if start == nums.len() {
        result.push(nums.to_vec());
        return;
    }

    for i in start..nums.len() {
        // 跳过重复元素（可选优化）
        if i != start && nums[i] == nums[start] {
            continue;
        }

        nums.swap(start, i);
        permute_backtrack(nums, start + 1, result);
        nums.swap(start, i); // 回溯
    }
}

/// 组合生成结果
pub type CombinationsResult<T> = Vec<Vec<T>>;

/// 生成所有k个元素的组合
///
/// 从n个元素中选择k个的所有组合
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(C(n,k)) = O(n!/(k!(n-k)!))
/// - **空间复杂度**：O(k) 递归栈
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking::generate_combinations;
///
/// let nums = vec![1, 2, 3, 4];
/// let combos = generate_combinations(&nums, 2);
///
/// assert_eq!(combos.len(), 6);
/// assert!(combos.contains(&vec![1, 2]));
/// assert!(combos.contains(&vec![3, 4]));
/// ```
pub fn generate_combinations<T: Clone>(nums: &[T], k: usize) -> CombinationsResult<T> {
    let mut result = Vec::new();
    let mut current = Vec::new();

    combine_backtrack(nums, k, 0, &mut current, &mut result);

    result
}

fn combine_backtrack<T: Clone>(
    nums: &[T],
    k: usize,
    start: usize,
    current: &mut Vec<T>,
    result: &mut Vec<Vec<T>>,
) {
    // 找到一个组合
    if current.len() == k {
        result.push(current.clone());
        return;
    }

    // 剪枝：剩余元素不够
    if start >= nums.len() || current.len() + (nums.len() - start) < k {
        return;
    }

    for i in start..nums.len() {
        current.push(nums[i].clone());
        combine_backtrack(nums, k, i + 1, current, result);
        current.pop();
    }
}

/// 子集生成结果
pub type SubsetsResult<T> = Vec<Vec<T>>;

/// 生成所有子集（幂集）
///
/// 返回给定集合的所有子集
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(2^n)
/// - **空间复杂度**：O(n)
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking::generate_subsets;
///
/// let nums = vec![1, 2, 3];
/// let subsets = generate_subsets(&nums);
///
/// assert_eq!(subsets.len(), 8); // 2^3
/// assert!(subsets.contains(&vec![]));
/// assert!(subsets.contains(&vec![1, 2, 3]));
/// ```
pub fn generate_subsets<T: Clone>(nums: &[T]) -> SubsetsResult<T> {
    let mut result = Vec::new();
    let mut current = Vec::new();

    subset_backtrack(nums, 0, &mut current, &mut result);

    result
}

fn subset_backtrack<T: Clone>(
    nums: &[T],
    start: usize,
    current: &mut Vec<T>,
    result: &mut Vec<Vec<T>>,
) {
    result.push(current.clone());

    for i in start..nums.len() {
        current.push(nums[i].clone());
        subset_backtrack(nums, i + 1, current, result);
        current.pop();
    }
}

/// 迷宫求解结果
#[derive(Debug, Clone, PartialEq)]
pub struct MazeResult {
    /// 是否找到路径
    pub found: bool,
    /// 路径坐标列表 (row, col)
    pub path: Vec<(usize, usize)>,
}

/// 迷宫求解
///
/// 在给定的迷宫中找到从起点到终点的路径
///
/// # 参数
///
/// * `maze` - 迷宫，0表示通路，1表示墙
/// * `start` - 起点 (row, col)
/// * `end` - 终点 (row, col)
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking::solve_maze;
///
/// let maze = vec![
///     vec![0, 1, 0, 0, 0],
///     vec![0, 1, 0, 1, 0],
///     vec![0, 0, 0, 1, 0],
///     vec![1, 1, 0, 0, 0],
///     vec![0, 0, 0, 1, 0],
/// ];
///
/// let result = solve_maze(&maze, (0, 0), (4, 4));
/// assert!(result.found);
/// assert_eq!(result.path[0], (0, 0));
/// assert_eq!(result.path.last().copied(), Some((4, 4)));
/// ```
pub fn solve_maze(
    maze: &[Vec<i32>],
    start: (usize, usize),
    end: (usize, usize),
) -> MazeResult {
    if maze.is_empty() || start.0 >= maze.len() || start.1 >= maze[0].len() {
        return MazeResult {
            found: false,
            path: vec![],
        };
    }

    let rows = maze.len();
    let cols = maze[0].len();
    let mut visited = vec![vec![false; cols]; rows];
    let mut path = Vec::new();

    if maze_backtrack(maze, start.0, start.1, end, &mut visited, &mut path) {
        MazeResult {
            found: true,
            path,
        }
    } else {
        MazeResult {
            found: false,
            path: vec![],
        }
    }
}

fn maze_backtrack(
    maze: &[Vec<i32>],
    row: usize,
    col: usize,
    end: (usize, usize),
    visited: &mut [Vec<bool>],
    path: &mut Vec<(usize, usize)>,
) -> bool {
    let rows = maze.len();
    let cols = maze[0].len();

    // 越界检查
    if row >= rows || col >= cols {
        return false;
    }

    // 墙或已访问
    if maze[row][col] == 1 || visited[row][col] {
        return false;
    }

    // 标记访问
    visited[row][col] = true;
    path.push((row, col));

    // 到达终点
    if (row, col) == end {
        return true;
    }

    // 尝试四个方向
    let directions = [(0, 1), (1, 0), (0, -1i32), (-1i32, 0)];
    for (dr, dc) in &directions {
        let new_row = row as i32 + dr;
        let new_col = col as i32 + dc;

        if new_row >= 0 && new_col >= 0 {
            if maze_backtrack(
                maze,
                new_row as usize,
                new_col as usize,
                end,
                visited,
                path,
            ) {
                return true;
            }
        }
    }

    // 回溯
    path.pop();
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subset_sum_found() {
        let nums = vec![3, 34, 4, 12, 5, 2];
        let result = subset_sum(&nums, 9);

        assert!(result.found);
        assert_eq!(result.values.iter().sum::<i64>(), 9);
    }

    #[test]
    fn test_subset_sum_not_found() {
        let nums = vec![1, 2, 3];
        let result = subset_sum(&nums, 10);

        assert!(!result.found);
        assert!(result.values.is_empty());
    }

    #[test]
    fn test_subset_sum_empty() {
        let nums: Vec<i64> = vec![];
        let result = subset_sum(&nums, 0);

        assert!(result.found);
        assert!(result.values.is_empty());
    }

    #[test]
    fn test_graph_coloring_simple() {
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C']);
        graph.insert('B', vec!['A']);
        graph.insert('C', vec!['A']);

        let result = graph_coloring(&graph, 2);
        assert!(result.colorable);
    }

    #[test]
    fn test_graph_coloring_complete_graph() {
        // 完全图K4需要4种颜色
        let mut graph: HashMap<char, Vec<char>> = HashMap::new();
        graph.insert('A', vec!['B', 'C', 'D']);
        graph.insert('B', vec!['A', 'C', 'D']);
        graph.insert('C', vec!['A', 'B', 'D']);
        graph.insert('D', vec!['A', 'B', 'C']);

        let result = graph_coloring(&graph, 3);
        assert!(!result.colorable);

        let result = graph_coloring(&graph, 4);
        assert!(result.colorable);
    }

    #[test]
    fn test_graph_coloring_empty() {
        let graph: HashMap<char, Vec<char>> = HashMap::new();
        let result = graph_coloring(&graph, 1);
        assert!(result.colorable);
    }

    #[test]
    fn test_generate_permutations() {
        let nums = vec![1, 2, 3];
        let perms = generate_permutations(&nums);

        assert_eq!(perms.len(), 6);
        assert!(perms.contains(&vec![1, 2, 3]));
        assert!(perms.contains(&vec![3, 2, 1]));
    }

    #[test]
    fn test_generate_permutations_empty() {
        let nums: Vec<i32> = vec![];
        let perms = generate_permutations(&nums);
        assert_eq!(perms, vec![Vec::<i32>::new()]);
    }

    #[test]
    fn test_generate_combinations() {
        let nums = vec![1, 2, 3, 4];
        let combos = generate_combinations(&nums, 2);

        assert_eq!(combos.len(), 6);
        assert!(combos.contains(&vec![1, 2]));
        assert!(combos.contains(&vec![3, 4]));
    }

    #[test]
    fn test_generate_subsets() {
        let nums = vec![1, 2, 3];
        let subsets = generate_subsets(&nums);

        assert_eq!(subsets.len(), 8);
        assert!(subsets.contains(&vec![]));
        assert!(subsets.contains(&vec![1, 2, 3]));
    }

    #[test]
    fn test_solve_maze() {
        let maze = vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 1, 0, 1, 0],
            vec![0, 0, 0, 1, 0],
            vec![1, 1, 0, 0, 0],
            vec![0, 0, 0, 1, 0],
        ];

        let result = solve_maze(&maze, (0, 0), (4, 4));
        assert!(result.found);
        assert_eq!(result.path[0], (0, 0));
        assert_eq!(result.path.last().copied(), Some((4, 4)));
    }

    #[test]
    fn test_solve_maze_no_path() {
        let maze = vec![
            vec![0, 1, 0],
            vec![0, 1, 0],
            vec![0, 1, 0],
        ];

        let result = solve_maze(&maze, (0, 0), (2, 2));
        assert!(!result.found);
    }

    #[test]
    fn test_solve_maze_start_is_end() {
        let maze = vec![vec![0]];
        let result = solve_maze(&maze, (0, 0), (0, 0));
        assert!(result.found);
        assert_eq!(result.path, vec![(0, 0)]);
    }
}
