//! LeetCode 70. 爬楼梯
//!
//! 假设你正在爬楼梯。需要 n 阶你才能到达楼顶。
//! 每次你可以爬 1 或 2 个台阶。你有多少种不同的方法可以爬到楼顶呢？
//!
//! 对标: LeetCode 70 / docs/13-LeetCode算法面试专题/06-面试专题/03-高频Top100-DP与贪心.md

/// 计算爬到第 n 阶楼梯的不同方法数。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`n` 范围 `[1, 45]`。
/// - **后置条件 (Post)**：返回从第 0 阶到达第 n 阶的不同方法总数。
///
/// # 核心思路
///
/// 动态规划：设 `dp[i]` 为到达第 i 阶的方法数。
/// 状态转移：`dp[i] = dp[i-1] + dp[i-2]`（最后一步跨 1 阶或 2 阶）。
/// 使用滚动变量将空间优化至 O(1)。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 单次遍历。
/// - **空间复杂度**：O(1) — 滚动变量。
///
/// # 证明要点
///
/// - 最优子结构：到达第 i 阶的最后一步只能是 1 阶（从 i-1）或 2 阶（从 i-2）。
///   因此方法数等于到达 i-1 和 i-2 的方法数之和。
/// - 无后效性：`dp[i]` 的值仅由前两个状态决定。
/// - 数学本质：`dp[n] = F_{n+1}`，即第 n+1 个斐波那契数。
pub fn climb_stairs(n: i32) -> i32 {
    if n <= 2 {
        return n;
    }
    let mut prev2 = 1;
    let mut prev1 = 2;
    for _ in 3..=n {
        let curr = prev1 + prev2;
        prev2 = prev1;
        prev1 = curr;
    }
    prev1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(climb_stairs(2), 2);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(climb_stairs(3), 3);
    }

    #[test]
    fn test_single_step() {
        assert_eq!(climb_stairs(1), 1);
    }

    #[test]
    fn test_four_steps() {
        assert_eq!(climb_stairs(4), 5);
    }

    #[test]
    fn test_fibonacci() {
        assert_eq!(climb_stairs(10), 89);
    }

    #[test]
    fn test_max_constraint() {
        assert_eq!(climb_stairs(45), 1836311903);
    }
}
