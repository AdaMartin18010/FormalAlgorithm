//! LeetCode 37. 解数独
//!
//! 编写一个程序，通过填充空格来解决数独问题。假设唯一解。
//!
//! 对标: LeetCode 37 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md

/// 原地修改 board，填充空格得到合法数独解。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`board` 为 9x9 的二维向量，元素为 `'1'`-`'9'` 或 `'.'`；输入保证有且仅有一个解。
/// - **后置条件 (Post)**：`board` 被原地修改为合法的完整数独，每行、每列、每个 3x3 宫格均包含 `'1'`-`'9'` 各一次。
///
/// # 回溯不变式
///
/// - 已填充的格子均满足数独约束（行、列、宫格唯一）。
/// - 未填充的格子标记为 `'.'`。
///
/// # 剪枝条件
///
/// 对于候选数字 `d`，若当前行、列或 3x3 宫格已包含 `d`，则剪枝。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(9^m) — m 为空格数，每个空格最多尝试 9 个数字。
/// - **空间复杂度**：O(m) — 递归栈深度最多为 m。
///
/// # 证明要点
/// - 终止性：每次递归填充一个空格，空格数严格递减，必在有限步内终止。
/// - 正确性：剪枝仅排除与已有约束冲突的数字，不会排除合法解；找到的第一个完整填充即为唯一解。
pub fn solve_sudoku(board: &mut Vec<Vec<char>>) {
    let mut rows = vec![0u16; 9];
    let mut cols = vec![0u16; 9];
    let mut boxes = vec![0u16; 9];
    let mut empty = Vec::new();

    for r in 0..9 {
        for c in 0..9 {
            let val = board[r][c];
            if val == '.' {
                empty.push((r, c));
            } else {
                let mask = 1 << (val as u8 - b'1');
                rows[r] |= mask;
                cols[c] |= mask;
                boxes[(r / 3) * 3 + (c / 3)] |= mask;
            }
        }
    }

    fn backtrack(
        idx: usize,
        empty: &[(usize, usize)],
        rows: &mut [u16],
        cols: &mut [u16],
        boxes: &mut [u16],
        board: &mut Vec<Vec<char>>,
    ) -> bool {
        if idx == empty.len() {
            return true;
        }
        let (r, c) = empty[idx];
        let box_idx = (r / 3) * 3 + (c / 3);
        for d in 0..9 {
            let mask = 1 << d;
            if rows[r] & mask != 0 || cols[c] & mask != 0 || boxes[box_idx] & mask != 0 {
                continue;
            }
            board[r][c] = (b'1' + d) as char;
            rows[r] |= mask;
            cols[c] |= mask;
            boxes[box_idx] |= mask;
            if backtrack(idx + 1, empty, rows, cols, boxes, board) {
                return true;
            }
            rows[r] ^= mask;
            cols[c] ^= mask;
            boxes[box_idx] ^= mask;
            board[r][c] = '.';
        }
        false
    }

    backtrack(0, &empty, &mut rows, &mut cols, &mut boxes, board);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example() {
        let mut board = vec![
            vec!['5','3','.','.','7','.','.','.','.'],
            vec!['6','.','.','1','9','5','.','.','.'],
            vec!['.','9','8','.','.','.','.','6','.'],
            vec!['8','.','.','.','6','.','.','.','3'],
            vec!['4','.','.','8','.','3','.','.','1'],
            vec!['7','.','.','.','2','.','.','.','6'],
            vec!['.','6','.','.','.','.','2','8','.'],
            vec!['.','.','.','4','1','9','.','.','5'],
            vec!['.','.','.','.','8','.','.','7','9'],
        ];
        solve_sudoku(&mut board);
        let expected = vec![
            vec!['5','3','4','6','7','8','9','1','2'],
            vec!['6','7','2','1','9','5','3','4','8'],
            vec!['1','9','8','3','4','2','5','6','7'],
            vec!['8','5','9','7','6','1','4','2','3'],
            vec!['4','2','6','8','5','3','7','9','1'],
            vec!['7','1','3','9','2','4','8','5','6'],
            vec!['9','6','1','5','3','7','2','8','4'],
            vec!['2','8','7','4','1','9','6','3','5'],
            vec!['3','4','5','2','8','6','1','7','9'],
        ];
        assert_eq!(board, expected);
    }
}
