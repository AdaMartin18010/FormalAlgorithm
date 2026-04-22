//! LeetCode 48. 旋转图像
//!
//! 给定一个 n × n 的二维矩阵 matrix 表示一个图像。请你将图像顺时针旋转 90 度。
//! 你必须在 原地 旋转图像，这意味着你需要直接修改输入的二维矩阵。
//! 请不要使用另一个矩阵来旋转图像。
//!
//! 对标: LeetCode 48 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

/// 原地顺时针旋转 n × n 矩阵 90 度。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`matrix` 为 n × n 方阵，n ≥ 1。
/// - **后置条件 (Post)**：`matrix` 被原地修改为顺时针旋转 90 度后的结果，
///   即原 `matrix[i][j]` 移动到 `matrix[j][n - 1 - i]`。
///
/// # 核心思路
///
/// 两步法（转置 + 水平翻转）：
/// 1. **转置**：沿主对角线交换元素，即 `matrix[i][j] ⟷ matrix[j][i]`。
/// 2. **水平翻转**：每行左右翻转，即 `matrix[i][j] ⟷ matrix[i][n - 1 - j]`。
///
/// 这两步的组合效果等价于顺时针旋转 90 度：
/// `(i, j) → (j, i) → (j, n - 1 - i)`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n²) — 遍历矩阵约一半元素进行转置，再遍历全部元素进行翻转。
/// - **空间复杂度**：O(1) — 仅使用常数额外空间，原地修改。
///
/// # 证明要点
///
/// - 转置将 `(i, j)` 映射到 `(j, i)`。
/// - 水平翻转将 `(j, i)` 映射到 `(j, n - 1 - i)`。
/// - 复合映射 `(i, j) → (j, n - 1 - i)` 正是顺时针旋转 90 度的坐标变换。
pub fn rotate(matrix: &mut Vec<Vec<i32>>) {
    let n = matrix.len();
    if n <= 1 {
        return;
    }

    // 步骤1：转置（沿主对角线交换）
    for i in 0..n {
        for j in (i + 1)..n {
            let tmp = matrix[i][j];
            matrix[i][j] = matrix[j][i];
            matrix[j][i] = tmp;
        }
    }

    // 步骤2：水平翻转（每行左右对称交换）
    for i in 0..n {
        for j in 0..(n / 2) {
            let tmp = matrix[i][j];
            matrix[i][j] = matrix[i][n - 1 - j];
            matrix[i][n - 1 - j] = tmp;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let mut matrix = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        rotate(&mut matrix);
        assert_eq!(matrix, vec![vec![7, 4, 1], vec![8, 5, 2], vec![9, 6, 3]]);
    }

    #[test]
    fn test_example_2() {
        let mut matrix = vec![
            vec![5, 1, 9, 11],
            vec![2, 4, 8, 10],
            vec![13, 3, 6, 7],
            vec![15, 14, 12, 16],
        ];
        rotate(&mut matrix);
        assert_eq!(
            matrix,
            vec![
                vec![15, 13, 2, 5],
                vec![14, 3, 4, 1],
                vec![12, 6, 8, 9],
                vec![16, 7, 10, 11],
            ]
        );
    }

    #[test]
    fn test_single_element() {
        let mut matrix = vec![vec![42]];
        rotate(&mut matrix);
        assert_eq!(matrix, vec![vec![42]]);
    }

    #[test]
    fn test_2x2() {
        let mut matrix = vec![vec![1, 2], vec![3, 4]];
        rotate(&mut matrix);
        assert_eq!(matrix, vec![vec![3, 1], vec![4, 2]]);
    }
}
