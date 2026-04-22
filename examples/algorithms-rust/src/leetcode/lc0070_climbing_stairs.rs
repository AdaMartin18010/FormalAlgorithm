//! LeetCode 70. Climbing Stairs
//! 链接: https://leetcode.com/problems/climbing-stairs/
//! 难度: Easy
//!
//! 题目描述:
//! 假设你正在爬楼梯。需要 n 阶你才能到达楼顶。每次你可以爬 1 或 2 个台阶。
//! 你有多少种不同的方法可以爬到楼顶呢？
//!
//! 形式化规约:
//!   输入: 整数 n（台阶数）
//!   输出: 爬到第 n 阶的方法数（每次可跨 1 或 2 阶）
//!
//! 最优解思路:
//!   dp[i] 表示到达第 i 阶的方法数。状态转移: dp[i] = dp[i-1] + dp[i-2]。
//!   使用滚动数组优化空间到 O(1)。
//!
//! 复杂度:
//!   时间: O(n)
//!   空间: O(1)
//!
//! 正确性要点:
//!   1. 斐波那契数列模型
//!   2. 边界: dp[0] = 1, dp[1] = 1
//!   3. 滚动数组只需维护前两个状态

pub struct Solution;

impl Solution {
    pub fn climb_stairs(n: i32) -> i32 {
        if n <= 1 {
            return 1;
        }

        let mut prev2 = 1; // dp[i-2]
        let mut prev1 = 1; // dp[i-1]

        for _ in 2..=n {
            let curr = prev1 + prev2;
            prev2 = prev1;
            prev1 = curr;
        }

        prev1
    }

    /// 矩阵快速幂优化，时间 O(log n)
    pub fn climb_stairs_fast(n: i32) -> i32 {
        if n <= 1 {
            return 1;
        }

        // 斐波那契的矩阵形式: [F(n), F(n-1)]^T = M^(n-1) * [F(1), F(0)]^T
        // 其中 M = [[1, 1], [1, 0]]
        let n = n as u64;
        let mat = [[1i64, 1i64], [1i64, 0i64]];
        let power = Self::matrix_pow(mat, n - 1);
        (power[0][0] + power[0][1]) as i32
    }

    fn matrix_mult(a: [[i64; 2]; 2], b: [[i64; 2]; 2]) -> [[i64; 2]; 2] {
        let mut c = [[0i64; 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                for k in 0..2 {
                    c[i][j] += a[i][k] * b[k][j];
                }
            }
        }
        c
    }

    fn matrix_pow(mut base: [[i64; 2]; 2], mut exp: u64) -> [[i64; 2]; 2] {
        let mut result = [[1i64, 0i64], [0i64, 1i64]]; // 单位矩阵
        while exp > 0 {
            if exp & 1 == 1 {
                result = Self::matrix_mult(result, base);
            }
            base = Self::matrix_mult(base, base);
            exp >>= 1;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_climb_stairs() {
        assert_eq!(Solution::climb_stairs(2), 2);
        assert_eq!(Solution::climb_stairs(3), 3);
        assert_eq!(Solution::climb_stairs(4), 5);
        assert_eq!(Solution::climb_stairs(1), 1);
        assert_eq!(Solution::climb_stairs(0), 1);
    }

    #[test]
    fn test_climb_stairs_fast() {
        assert_eq!(Solution::climb_stairs_fast(2), 2);
        assert_eq!(Solution::climb_stairs_fast(3), 3);
        assert_eq!(Solution::climb_stairs_fast(10), 89);
    }
}
