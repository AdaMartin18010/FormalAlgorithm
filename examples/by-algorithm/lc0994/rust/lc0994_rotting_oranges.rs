//! LeetCode 994. Rotting Oranges
//! 链接: https://leetcode.com/problems/rotting-oranges/
//! 难度: Medium
//!
//! 算法: 多源 BFS
//! 时间复杂度: O(m * n)
//! 空间复杂度: O(m * n)

use std::collections::VecDeque;

pub struct Solution;

impl Solution {
    /// 返回腐烂所有新鲜橘子所需的最短分钟数。
    ///
    /// 形式化规约:
    /// - 前置条件: grid 为 m×n 的矩阵，元素 ∈ {0, 1, 2}
    /// - 后置条件: 返回最短时间，若无法全部腐烂则返回 -1
    pub fn oranges_rotting(grid: Vec<Vec<i32>>) -> i32 {
        let m = grid.len();
        if m == 0 {
            return 0;
        }
        let n = grid[0].len();
        
        let mut queue: VecDeque<(usize, usize, i32)> = VecDeque::new();
        let mut fresh_count = 0;
        
        // 初始化: 将所有腐烂橘子入队（多源 BFS 的第 0 层）
        for r in 0..m {
            for c in 0..n {
                match grid[r][c] {
                    2 => queue.push_back((r, c, 0)),
                    1 => fresh_count += 1,
                    _ => {}
                }
            }
        }
        
        if fresh_count == 0 {
            return 0;
        }
        
        let mut grid = grid;
        let mut minutes = 0;
        let dirs = [(0, 1), (0, -1), (1, 0), (-1, 0)];
        
        // 多源 BFS
        while let Some((r, c, t)) = queue.pop_front() {
            minutes = minutes.max(t);
            
            for (dr, dc) in &dirs {
                let nr = r as i32 + dr;
                let nc = c as i32 + dc;
                
                if nr < 0 || nr >= m as i32 || nc < 0 || nc >= n as i32 {
                    continue;
                }
                
                let nr = nr as usize;
                let nc = nc as usize;
                
                if grid[nr][nc] == 1 {
                    // 新鲜橘子腐烂
                    grid[nr][nc] = 2;
                    fresh_count -= 1;
                    queue.push_back((nr, nc, t + 1));
                }
            }
        }
        
        if fresh_count == 0 {
            minutes
        } else {
            -1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_oranges_rotting_basic() {
        let grid = vec![
            vec![2, 1, 1],
            vec![1, 1, 0],
            vec![0, 1, 1],
        ];
        assert_eq!(Solution::oranges_rotting(grid), 4);
    }

    #[test]
    fn test_oranges_rotting_impossible() {
        let grid = vec![
            vec![2, 1, 1],
            vec![0, 1, 1],
            vec![1, 0, 1],
        ];
        assert_eq!(Solution::oranges_rotting(grid), -1);
    }

    #[test]
    fn test_oranges_rotting_no_fresh() {
        let grid = vec![
            vec![0, 2],
        ];
        assert_eq!(Solution::oranges_rotting(grid), 0);
    }
}
