//! LeetCode 51. N 皇后
//!
//! 在 n×n 的棋盘上放置 n 个皇后，使它们不能互相攻击，返回所有 distinct 的解法。
//!
//! 对标: LeetCode 51 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md

/// 返回 n 皇后问题的所有解。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`1 <= n <= 9`。
/// - **后置条件 (Post)**：返回所有 distinct 的棋盘布局，每个布局为 n 个字符串的向量，
///   任意两个皇后不在同一行、同一列、同一斜线。
///
/// # 回溯不变式
///
/// 设当前正在处理第 `row` 行，已放置皇后的列集合为 `cols`，主对角线集合为 `diag1`，副对角线集合为 `diag2`。
/// - 已放置的皇后互不攻击。
/// - 第 0 到 `row-1` 行每行恰好有一个皇后。
///
/// # 剪枝条件
///
/// 对于候选列 `col`，若满足 `col in cols` 或 `(row - col) in diag1` 或 `(row + col) in diag2`，则剪枝。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n!) — 第 0 行有 n 种选择，第 1 行最多 n-1 种，依此类推。
/// - **空间复杂度**：O(n) — 递归栈深度为 n，加上集合空间。
///
/// # 证明要点
/// - 不遗漏：逐行枚举所有合法列位置，DFS 遍历全部可行解空间。
/// - 剪枝正确性：若 `col` 与已有皇后同列或同对角线，后续无论如何放置都会冲突，剪去该分支安全。
pub fn solve_n_queens(n: i32) -> Vec<Vec<String>> {
    let n = n as usize;
    let mut result: Vec<Vec<String>> = Vec::new();
    let mut board: Vec<usize> = Vec::with_capacity(n);

    fn backtrack(
        n: usize,
        row: usize,
        cols: i32,
        diag1: i32,
        diag2: i32,
        board: &mut Vec<usize>,
        result: &mut Vec<Vec<String>>,
    ) {
        if row == n {
            let mut solution = Vec::with_capacity(n);
            for &c in board.iter() {
                let mut row_str = vec!['.'; n];
                row_str[c] = 'Q';
                solution.push(row_str.into_iter().collect());
            }
            result.push(solution);
            return;
        }

        let mut available = ((1 << n) - 1) & !(cols | diag1 | diag2);
        while available != 0 {
            let lsb = available & -available;
            let col = lsb.trailing_zeros() as usize;
            board.push(col);
            backtrack(
                n,
                row + 1,
                cols | lsb,
                (diag1 | lsb) << 1,
                (diag2 | lsb) >> 1,
                board,
                result,
            );
            board.pop();
            available &= available - 1;
        }
    }

    backtrack(n, 0, 0, 0, 0, &mut board, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_n_4() {
        let result = solve_n_queens(4);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&vec![
            ".Q..".to_string(),
            "...Q".to_string(),
            "Q...".to_string(),
            "..Q.".to_string(),
        ]));
        assert!(result.contains(&vec![
            "..Q.".to_string(),
            "Q...".to_string(),
            "...Q".to_string(),
            ".Q..".to_string(),
        ]));
    }

    #[test]
    fn test_n_1() {
        assert_eq!(solve_n_queens(1), vec![vec!["Q".to_string()]]);
    }

    #[test]
    fn test_n_2_no_solution() {
        assert!(solve_n_queens(2).is_empty());
    }

    #[test]
    fn test_n_3_no_solution() {
        assert!(solve_n_queens(3).is_empty());
    }

    #[test]
    fn test_n_8() {
        assert_eq!(solve_n_queens(8).len(), 92);
    }
}
