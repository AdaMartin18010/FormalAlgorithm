//! N皇后问题 - 回溯算法实现
//!
//! N皇后问题是一个经典的回溯算法问题，要求在N×N的棋盘上放置N个皇后，
//! 使得它们互不攻击（即任意两个皇后不在同一行、同一列或同一对角线上）。


/// N皇后问题的解
#[derive(Debug, Clone, PartialEq)]
pub struct NQueensSolution {
    /// 棋盘大小
    pub n: usize,
    /// 皇后位置，queens[i] 表示第i行皇后所在的列
    pub queens: Vec<usize>,
    /// 解的字符串表示
    pub board: Vec<String>,
}

impl NQueensSolution {
    /// 从queens数组创建解
    fn from_queens(n: usize, queens: Vec<usize>) -> Self {
        let board = Self::format_board(n, &queens);
        NQueensSolution { n, queens, board }
    }

    /// 格式化棋盘为字符串
    fn format_board(n: usize, queens: &[usize]) -> Vec<String> {
        let mut board = Vec::with_capacity(n);
        for &col in queens.iter().take(n) {
            let mut row = vec!['.'; n];
            if col < n {
                row[col] = 'Q';
            }
            board.push(row.into_iter().collect());
        }
        board
    }

    /// 打印棋盘
    pub fn print(&self) {
        println!("{}-Queens Solution:", self.n);
        for row in &self.board {
            println!(" {}", row);
        }
    }
}

/// 求解N皇后问题（返回所有解）
///
/// # 算法说明
///
/// N皇后问题使用回溯算法求解：
/// 1. 逐行放置皇后
/// 2. 在当前行尝试每一列
/// 3. 如果位置安全（不与已放置皇后冲突），放置皇后并递归下一行
/// 4. 如果无法放置，回溯并尝试下一列
/// 5. 当所有行都放置成功，找到一个解
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(N!) - 最坏情况需要尝试所有排列
/// - **空间复杂度**：O(N) - 递归栈和存储解
///
/// # 参数
///
/// * `n` - 棋盘大小和皇后数量
///
/// # 返回值
///
/// 返回所有解的列表，如果没有解返回空列表
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::solve_n_queens;
///
/// let solutions = solve_n_queens(4);
/// assert_eq!(solutions.len(), 2);
///
/// // 验证解的正确性
/// for sol in &solutions {
///     assert_eq!(sol.queens.len(), 4);
/// }
/// ```
pub fn solve_n_queens(n: usize) -> Vec<NQueensSolution> {
    if n == 0 {
        return vec![];
    }

    let mut solutions = Vec::new();
    let mut queens = vec![0; n];
    let mut columns = vec![false; n];
    let mut diagonals1 = vec![false; 2 * n - 1]; // 主对角线 (row - col + n - 1)
    let mut diagonals2 = vec![false; 2 * n - 1]; // 副对角线 (row + col)

    backtrack(
        n,
        0,
        &mut queens,
        &mut columns,
        &mut diagonals1,
        &mut diagonals2,
        &mut solutions,
    );

    solutions
}

/// 回溯求解
fn backtrack(
    n: usize,
    row: usize,
    queens: &mut Vec<usize>,
    columns: &mut Vec<bool>,
    diagonals1: &mut Vec<bool>,
    diagonals2: &mut Vec<bool>,
    solutions: &mut Vec<NQueensSolution>,
) {
    if row == n {
        // 找到一个解
        solutions.push(NQueensSolution::from_queens(n, queens.clone()));
        return;
    }

    for col in 0..n {
        let d1 = row + col; // 副对角线索引
        let d2 = row + n - 1 - col; // 主对角线索引（使用另一种计算方式）

        // 检查冲突
        if columns[col] || diagonals1[d1] || diagonals2[d2] {
            continue;
        }

        // 放置皇后
        queens[row] = col;
        columns[col] = true;
        diagonals1[d1] = true;
        diagonals2[d2] = true;

        // 递归下一行
        backtrack(
            n,
            row + 1,
            queens,
            columns,
            diagonals1,
            diagonals2,
            solutions,
        );

        // 回溯
        columns[col] = false;
        diagonals1[d1] = false;
        diagonals2[d2] = false;
    }
}

/// 求解N皇后问题（只返回一个解）
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::solve_n_queens_one;
///
/// let solution = solve_n_queens_one(8);
/// assert!(solution.is_some());
/// let sol = solution.unwrap();
/// assert_eq!(sol.n, 8);
/// ```
pub fn solve_n_queens_one(n: usize) -> Option<NQueensSolution> {
    if n == 0 {
        return None;
    }

    let mut queens = vec![0; n];
    let mut columns = vec![false; n];
    let mut diagonals1 = vec![false; 2 * n - 1];
    let mut diagonals2 = vec![false; 2 * n - 1];

    if backtrack_one(
        n,
        0,
        &mut queens,
        &mut columns,
        &mut diagonals1,
        &mut diagonals2,
    ) {
        Some(NQueensSolution::from_queens(n, queens))
    } else {
        None
    }
}

/// 回溯求解（只找一个解）
fn backtrack_one(
    n: usize,
    row: usize,
    queens: &mut Vec<usize>,
    columns: &mut Vec<bool>,
    diagonals1: &mut Vec<bool>,
    diagonals2: &mut Vec<bool>,
) -> bool {
    if row == n {
        return true;
    }

    for col in 0..n {
        let d1 = row + col;
        let d2 = row + n - 1 - col;

        if columns[col] || diagonals1[d1] || diagonals2[d2] {
            continue;
        }

        queens[row] = col;
        columns[col] = true;
        diagonals1[d1] = true;
        diagonals2[d2] = true;

        if backtrack_one(n, row + 1, queens, columns, diagonals1, diagonals2) {
            return true;
        }

        columns[col] = false;
        diagonals1[d1] = false;
        diagonals2[d2] = false;
    }

    false
}

/// 统计N皇后问题的解的数量
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::count_n_queens_solutions;
///
/// assert_eq!(count_n_queens_solutions(1), 1);
/// assert_eq!(count_n_queens_solutions(2), 0);
/// assert_eq!(count_n_queens_solutions(3), 0);
/// assert_eq!(count_n_queens_solutions(4), 2);
/// assert_eq!(count_n_queens_solutions(8), 92);
/// ```
pub fn count_n_queens_solutions(n: usize) -> usize {
    if n == 0 {
        return 0;
    }

    let mut count = 0;
    let mut queens = vec![0; n];
    let mut columns = vec![false; n];
    let mut diagonals1 = vec![false; 2 * n - 1];
    let mut diagonals2 = vec![false; 2 * n - 1];

    count_backtrack(
        n,
        0,
        &mut queens,
        &mut columns,
        &mut diagonals1,
        &mut diagonals2,
        &mut count,
    );

    count
}

fn count_backtrack(
    n: usize,
    row: usize,
    queens: &mut Vec<usize>,
    columns: &mut Vec<bool>,
    diagonals1: &mut Vec<bool>,
    diagonals2: &mut Vec<bool>,
    count: &mut usize,
) {
    if row == n {
        *count += 1;
        return;
    }

    for col in 0..n {
        let d1 = row + col;
        let d2 = row + n - 1 - col;

        if columns[col] || diagonals1[d1] || diagonals2[d2] {
            continue;
        }

        queens[row] = col;
        columns[col] = true;
        diagonals1[d1] = true;
        diagonals2[d2] = true;

        count_backtrack(
            n,
            row + 1,
            queens,
            columns,
            diagonals1,
            diagonals2,
            count,
        );

        columns[col] = false;
        diagonals1[d1] = false;
        diagonals2[d2] = false;
    }
}

/// 验证N皇后解是否有效
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::{solve_n_queens, is_valid_solution};
///
/// let solutions = solve_n_queens(4);
/// for sol in &solutions {
///     assert!(is_valid_solution(&sol.queens));
/// }
/// ```
pub fn is_valid_solution(queens: &[usize]) -> bool {
    let n = queens.len();

    for i in 0..n {
        for j in (i + 1)..n {
            // 检查是否在同一列
            if queens[i] == queens[j] {
                return false;
            }
            // 检查是否在同一对角线
            let diff = (queens[i] as i32 - queens[j] as i32).abs();
            if diff == (j - i) as i32 {
                return false;
            }
        }
    }

    true
}

/// 使用位运算优化的N皇后求解（适用于较大N值）
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::count_n_queens_bitwise;
///
/// assert_eq!(count_n_queens_bitwise(8), 92);
/// ```
pub fn count_n_queens_bitwise(n: usize) -> usize {
    if n == 0 || n > 32 {
        return 0;
    }

    let all = (1 << n) - 1; // n个1
    let mut count = 0;

    fn backtrack_bitwise(row: usize, hills: u32, next_row: u32, dales: u32, all: u32, count: &mut usize, n: usize) {
        if row == n {
            *count += 1;
            return;
        }

        // 计算当前行可放置皇后的位置
        let mut free_positions = !(hills | next_row | dales) & all;

        while free_positions != 0 {
            // 获取最低位的1
            let curr_pos = free_positions & (!free_positions + 1);
            free_positions ^= curr_pos;

            backtrack_bitwise(
                row + 1,
                (hills | curr_pos) << 1,
                next_row | curr_pos,
                (dales | curr_pos) >> 1,
                all,
                count,
                n,
            );
        }
    }

    backtrack_bitwise(0, 0, 0, 0, all, &mut count, n);
    count
}

/// 求解N皇后问题（使用迭代器风格的API）
///
/// 这是solve_n_queens的别名，提供一致的API风格
///
/// # 示例
///
/// ```
/// use formal_algorithms::backtracking_nqueens::solve_n_queens_iter;
///
/// let solutions: Vec<_> = solve_n_queens_iter(4);
/// assert_eq!(solutions.len(), 2);
/// ```
pub fn solve_n_queens_iter(n: usize) -> Vec<NQueensSolution> {
    solve_n_queens(n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_n_queens_1() {
        let solutions = solve_n_queens(1);
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].queens, vec![0]);
    }

    #[test]
    fn test_n_queens_2() {
        let solutions = solve_n_queens(2);
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_n_queens_3() {
        let solutions = solve_n_queens(3);
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_n_queens_4() {
        let solutions = solve_n_queens(4);
        assert_eq!(solutions.len(), 2);

        // 验证所有解
        for sol in &solutions {
            assert!(is_valid_solution(&sol.queens));
            assert_eq!(sol.queens.len(), 4);
        }
    }

    #[test]
    fn test_n_queens_5() {
        let solutions = solve_n_queens(5);
        assert_eq!(solutions.len(), 10);
    }

    #[test]
    fn test_n_queens_8() {
        let solutions = solve_n_queens(8);
        assert_eq!(solutions.len(), 92);
    }

    #[test]
    fn test_solve_one() {
        let solution = solve_n_queens_one(8);
        assert!(solution.is_some());
        let sol = solution.unwrap();
        assert!(is_valid_solution(&sol.queens));
    }

    #[test]
    fn test_solve_one_impossible() {
        let solution = solve_n_queens_one(2);
        assert!(solution.is_none());
    }

    #[test]
    fn test_count_solutions() {
        assert_eq!(count_n_queens_solutions(1), 1);
        assert_eq!(count_n_queens_solutions(2), 0);
        assert_eq!(count_n_queens_solutions(3), 0);
        assert_eq!(count_n_queens_solutions(4), 2);
        assert_eq!(count_n_queens_solutions(5), 10);
        assert_eq!(count_n_queens_solutions(6), 4);
        assert_eq!(count_n_queens_solutions(7), 40);
        assert_eq!(count_n_queens_solutions(8), 92);
    }

    #[test]
    fn test_is_valid_solution() {
        // 有效解
        assert!(is_valid_solution(&[1, 3, 0, 2])); // 4皇后解

        // 无效解 - 同列
        assert!(!is_valid_solution(&[0, 0, 0, 0]));

        // 无效解 - 对角线
        assert!(!is_valid_solution(&[0, 1, 2, 3]));
    }

    #[test]
    fn test_bitwise_count() {
        assert_eq!(count_n_queens_bitwise(1), 1);
        assert_eq!(count_n_queens_bitwise(2), 0);
        assert_eq!(count_n_queens_bitwise(4), 2);
        assert_eq!(count_n_queens_bitwise(8), 92);
    }

    #[test]
    fn test_iterator() {
        let solutions = solve_n_queens_iter(4);
        assert_eq!(solutions.len(), 2);

        for sol in &solutions {
            assert!(is_valid_solution(&sol.queens));
        }
    }

    #[test]
    fn test_empty_n() {
        let solutions = solve_n_queens(0);
        assert!(solutions.is_empty());
    }

    #[test]
    fn test_solution_format() {
        let solution = solve_n_queens_one(4).unwrap();
        assert_eq!(solution.board.len(), 4);

        for row in &solution.board {
            assert_eq!(row.len(), 4);
            assert!(row.contains('Q'));
        }
    }

    #[test]
    fn test_compare_methods() {
        // 比较三种方法的结果
        for n in 1..=8 {
            let solutions = solve_n_queens(n);
            let count = count_n_queens_solutions(n);
            let bitwise_count = count_n_queens_bitwise(n);

            assert_eq!(solutions.len(), count);
            assert_eq!(count, bitwise_count);
        }
    }
}
