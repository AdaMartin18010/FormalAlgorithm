//! LeetCode 62. 不同路径
//!
//! 一个机器人位于一个 m × n 网格的左上角（起始点在下图中标记为 "Start" ）。
//! 机器人每次只能向下或者向右移动一步。机器人试图达到网格的右下角（在下图中标记为 "Finish" ）。
//! 问总共有多少条不同的路径？
//!
//! 对标: LeetCode 62 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

/// 计算从网格左上角到右下角的不同路径总数（只能向右或向下）。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`1 ≤ m, n ≤ 100`。
/// - **后置条件 (Post)**：返回从 `(0, 0)` 到 `(m - 1, n - 1)` 的不同路径数。
///
/// # 核心思路
///
/// 组合数学：从起点到终点共需走 `(m - 1) + (n - 1) = m + n - 2` 步，
/// 其中恰好有 `m - 1` 步向下（或 `n - 1` 步向右）。
/// 路径总数即为从 `m + n - 2` 步中选择 `m - 1` 步向下的组合数：
///
/// `C(m + n - 2, m - 1) = (m + n - 2)! / ((m - 1)! · (n - 1)!)`
///
/// 为避免阶乘溢出，使用递推计算：
/// `C(a, b) = a · (a - 1) · ... · (a - b + 1) / b!`，其中 `a = m + n - 2, b = min(m - 1, n - 1)`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(min(m, n)) — 只需计算 min(m, n) 次乘除。
/// - **空间复杂度**：O(1) — 仅使用常数额外变量。
///
/// # 证明要点
///
/// - 每条唯一路径对应一个由 `m - 1` 个 "D" 和 `n - 1` 个 "R" 组成的唯一序列。
/// - 序列总数即为多重集排列数，等于二项式系数 `C(m + n - 2, m - 1)`。
/// - 递推过程中分子分母交替计算，确保中间结果不溢出（在题目约束下结果可放入 i32）。
pub fn unique_paths(m: i32, n: i32) -> i32 {
    let m = m as i64;
    let n = n as i64;
    let total = m + n - 2;
    let k = std::cmp::min(m - 1, n - 1);

    let mut result = 1i64;
    for i in 0..k {
        result = result * (total - i) / (i + 1);
    }
    result as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(unique_paths(3, 7), 28);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(unique_paths(3, 2), 3);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(unique_paths(7, 3), 28);
    }

    #[test]
    fn test_example_4() {
        assert_eq!(unique_paths(3, 3), 6);
    }

    #[test]
    fn test_1x1() {
        assert_eq!(unique_paths(1, 1), 1);
    }

    #[test]
    fn test_1xn() {
        assert_eq!(unique_paths(1, 100), 1);
    }

    #[test]
    fn test_mx1() {
        assert_eq!(unique_paths(100, 1), 1);
    }

    #[test]
    fn test_2x2() {
        assert_eq!(unique_paths(2, 2), 2);
    }
}
