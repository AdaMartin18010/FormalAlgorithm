//! LeetCode 200. 岛屿数量
//!
//! 给你一个由 '1'（陆地）和 '0'（水）组成的二维网格 grid，
//! 请你计算网格中岛屿的数量。
//!
//! 对标: LeetCode 200 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md

/// 计算二维网格中岛屿的数量。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`grid` 为 m × n 字符矩阵，m, n 范围 `[1, 300]`。
/// - **后置条件 (Post)**：返回由 '1' 组成的连通块数量（四连通）。
///
/// # 核心思路
///
/// DFS / Flood Fill：遍历网格，每当遇到未访问的 '1'，启动 DFS
/// 将与之连通的所有 '1' 标记为已访问（改为 '0'），岛屿计数加 1。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m * n) — 每个格子最多被访问一次。
/// - **空间复杂度**：O(m * n) — DFS 递归栈最坏情况（全为陆地）。
///
/// # 证明要点
///
/// - 不变式：已被清零的 '1' 均属于某个已计数的岛屿。
/// - 当遇到新的 '1' 时，它与所有已处理的格子均不连通（否则已被清零），
///   因此它必属于一个新的岛屿。
/// - DFS 将它的整个连通块清零，保证不会重复计数。
/// - 最终所有 '1' 都被清零，计数等于连通块数量。
pub fn num_islands(grid: Vec<Vec<char>>) -> i32 {
    let mut grid = grid;
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    let mut count = 0;

    fn dfs(grid: &mut Vec<Vec<char>>, r: i32, c: i32, m: i32, n: i32) {
        if r < 0 || r >= m || c < 0 || c >= n || grid[r as usize][c as usize] == '0' {
            return;
        }
        grid[r as usize][c as usize] = '0';
        dfs(grid, r + 1, c, m, n);
        dfs(grid, r - 1, c, m, n);
        dfs(grid, r, c + 1, m, n);
        dfs(grid, r, c - 1, m, n);
    }

    for i in 0..m {
        for j in 0..n {
            if grid[i][j] == '1' {
                count += 1;
                dfs(&mut grid, i as i32, j as i32, m as i32, n as i32);
            }
        }
    }

    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let grid = vec![
            vec!['1', '1', '1', '1', '0'],
            vec!['1', '1', '0', '1', '0'],
            vec!['1', '1', '0', '0', '0'],
            vec!['0', '0', '0', '0', '0'],
        ];
        assert_eq!(num_islands(grid), 1);
    }

    #[test]
    fn test_example_2() {
        let grid = vec![
            vec!['1', '1', '0', '0', '0'],
            vec!['1', '1', '0', '0', '0'],
            vec!['0', '0', '1', '0', '0'],
            vec!['0', '0', '0', '1', '1'],
        ];
        assert_eq!(num_islands(grid), 3);
    }

    #[test]
    fn test_all_water() {
        assert_eq!(num_islands(vec![vec!['0']]), 0);
    }

    #[test]
    fn test_single_land() {
        assert_eq!(num_islands(vec![vec!['1']]), 1);
    }

    #[test]
    fn test_separated() {
        assert_eq!(num_islands(vec![vec!['1', '0', '1']]), 2);
    }
}
