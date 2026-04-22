//! LeetCode 994. 腐烂的橘子
//!
//! 在给定的网格中，0 表示空单元格，1 表示新鲜橘子，2 表示腐烂橘子。
//! 每分钟，腐烂橘子会使上下左右相邻的新鲜橘子腐烂。
//! 返回直到没有新鲜橘子为止所需的最小分钟数，若无法使所有橘子腐烂则返回 -1。
//!
//! 对标: LeetCode 994 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md

use std::collections::VecDeque;

/// 返回所有新鲜橘子腐烂所需的最小分钟数。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`grid` 为 m × n 的二维向量，元素为 0、1 或 2；`1 <= m, n <= 10`。
/// - **后置条件 (Post)**：返回最小分钟数，若存在无法腐烂的新鲜橘子则返回 -1。
///
/// # BFS 层级不变式
///
/// 第 t 分钟时，队列中恰好包含第 t 分钟新腐烂的所有橘子。
/// 即 BFS 第 d 层对应第 d 分钟新腐烂的橘子集合。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(m × n) — 每个单元格最多入队一次。
/// - **空间复杂度**：O(m × n) — 队列最多包含所有单元格。
///
/// # 证明要点
/// - 多源 BFS 的正确性：所有初始腐烂橘子同时开始扩散，BFS 层数即为时间步。
/// - 最短性：BFS 保证每个新鲜橘子被最早到达的腐烂源腐烂，即最小时间。
/// - 终止判断：BFS 结束后检查是否还有新鲜橘子剩余。
pub fn oranges_rotting(grid: &mut Vec<Vec<i32>>) -> i32 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    let mut queue = VecDeque::new();
    let mut fresh = 0;

    for r in 0..m {
        for c in 0..n {
            match grid[r][c] {
                2 => queue.push_back((r, c, 0)),
                1 => fresh += 1,
                _ => {}
            }
        }
    }

    if fresh == 0 {
        return 0;
    }

    let mut minutes = 0;
    let directions = [(0, 1), (0, -1), (1, 0), (-1, 0)];

    while let Some((r, c, t)) = queue.pop_front() {
        minutes = minutes.max(t);
        for (dr, dc) in directions {
            let nr = r as isize + dr;
            let nc = c as isize + dc;
            if nr >= 0 && nr < m as isize && nc >= 0 && nc < n as isize {
                let (nr, nc) = (nr as usize, nc as usize);
                if grid[nr][nc] == 1 {
                    grid[nr][nc] = 2;
                    fresh -= 1;
                    queue.push_back((nr, nc, t + 1));
                }
            }
        }
    }

    if fresh == 0 { minutes } else { -1 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let mut grid = vec![
            vec![2, 1, 1],
            vec![1, 1, 0],
            vec![0, 1, 1],
        ];
        assert_eq!(oranges_rotting(&mut grid), 4);
    }

    #[test]
    fn test_leetcode_example_2() {
        let mut grid = vec![
            vec![2, 1, 1],
            vec![0, 1, 1],
            vec![1, 0, 1],
        ];
        assert_eq!(oranges_rotting(&mut grid), -1);
    }

    #[test]
    fn test_no_fresh() {
        let mut grid = vec![vec![0, 2]];
        assert_eq!(oranges_rotting(&mut grid), 0);
    }

    #[test]
    fn test_single_fresh() {
        let mut grid = vec![vec![1]];
        assert_eq!(oranges_rotting(&mut grid), -1);
    }

    #[test]
    fn test_single_rotten() {
        let mut grid = vec![vec![2]];
        assert_eq!(oranges_rotting(&mut grid), 0);
    }
}
