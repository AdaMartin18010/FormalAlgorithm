//! LeetCode 70. 爬楼梯 / Climbing Stairs
//!
//! 假设你正在爬楼梯。需要 n 阶你才能到达楼顶。
//! 每次你可以爬 1 或 2 个台阶。你有多少种不同的方法可以爬到楼顶呢？
//!
//! 题目链接: <https://leetcode.com/problems/climbing-stairs/>
//! 难度: Easy
//!
//! 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.1
//!
//! ## 形式化规约
//!
//! - **输入**: 整数 $n \in [1, 45]$
//! - **输出**: 爬到第 $n$ 阶的不同方法总数
//! - **前置条件**: $n \geq 1$
//! - **后置条件**: 返回值等于所有由 1 和 2 组成、和为 $n$ 的序列个数
//!
//! ## 状态转移方程
//!
//! $$ dp[i] = dp[i-1] + dp[i-2] $$
//!
//! - $dp[i-1]$: 最后一步跨 1 阶的方法数
//! - $dp[i-2]$: 最后一步跨 2 阶的方法数
//!
//! ## 最优子结构引理
//!
//! **引理** (最优子结构): 设 $f(n)$ 为爬到第 $n$ 阶的方法数，则
//! $$ f(n) = f(n-1) + f(n-2) $$
//!
//! **证明**: 到达第 $n$ 阶的最后一步只能是：
//! - 从第 $n-1$ 阶跨 1 阶上来，方法数为 $f(n-1)$
//! - 从第 $n-2$ 阶跨 2 阶上来，方法数为 $f(n-2)$
//! 这两种情况互斥且完备，故 $f(n) = f(n-1) + f(n-2)$。$\square$

/// 计算爬到第 n 阶楼梯的不同方法数。
///
/// # 参数
///
/// * `n` - 目标台阶数，范围 `[1, 45]`
///
/// # 返回值
///
/// 爬到第 n 阶的不同方法数。
///
/// # 复杂度分析
///
/// | 指标 | 值 | 说明 |
/// |------|-----|------|
/// | 时间复杂度 | $O(n)$ | 单次遍历 |
/// | 空间复杂度 | $O(1)$ | 滚动变量，仅保存前两个状态 |
///
/// # 正确性证明
///
/// **定理**: 算法返回 $f(n)$，即爬到第 $n$ 阶的方法数。
///
/// **证明** (数学归纳法):
///
/// - **基例**: $n = 1$ 时返回 1（只有 [1]），$n = 2$ 时返回 2（[1,1], [2]），均正确。
/// - **归纳假设**: 假设算法对所有 $k < n$ 正确返回 $f(k)$。
/// - **归纳步骤**: 对 $n \geq 3$，算法维护 `prev2 = f(n-2)`, `prev1 = f(n-1)`，
///   计算 `curr = prev1 + prev2 = f(n-1) + f(n-2) = f(n)`（由引理）。
///   因此算法正确返回 $f(n)$。$\square$
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
        // f(10) = F_11 = 89
        assert_eq!(climb_stairs(10), 89);
    }

    #[test]
    fn test_max_constraint() {
        assert_eq!(climb_stairs(45), 1836311903);
    }
}
