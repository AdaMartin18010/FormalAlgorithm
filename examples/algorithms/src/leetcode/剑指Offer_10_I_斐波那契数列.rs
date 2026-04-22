/// 剑指 Offer 10-I. 斐波那契数列
/// https://leetcode.cn/problems/fei-bo-na-qi-shu-lie-lcof/
///
/// Problem: Write a function to calculate the n-th Fibonacci number.
/// F(0) = 0, F(1) = 1, F(n) = F(n-1) + F(n-2) for n >= 2.
/// Result modulo 1_000_000_007.
///
/// Formal specification:
/// - Pre: n >= 0
/// - Post: result = F(n) mod 1_000_000_007
///
/// Algorithm: Iterative DP with O(n) time, O(1) space.
/// Proof by induction: Base cases trivial.
/// Inductive step: assume prev1 = F(i-1), prev2 = F(i-2).
/// Then curr = prev1 + prev2 = F(i-1) + F(i-2) = F(i).
///
/// Reference: docs/面试指南/06-面试专题/04-剑指Offer精选形式化证明.md

const MOD: i32 = 1_000_000_007;

pub fn fib(n: i32) -> i32 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut prev2: i64 = 0;
    let mut prev1: i64 = 1;

    for _ in 2..=n {
        let curr = (prev1 + prev2) % MOD as i64;
        prev2 = prev1;
        prev1 = curr;
    }

    prev1 as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base_cases() {
        assert_eq!(fib(0), 0);
        assert_eq!(fib(1), 1);
        assert_eq!(fib(2), 1);
    }

    #[test]
    fn test_small() {
        assert_eq!(fib(5), 5);
        assert_eq!(fib(10), 55);
    }

    #[test]
    fn test_large() {
        assert_eq!(fib(45), 1_134_903_170); // F(45) mod MOD
    }
}
