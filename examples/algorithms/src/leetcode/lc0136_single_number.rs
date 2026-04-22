//! LeetCode 136. Single Number
//! 链接: https://leetcode.com/problems/single-number/
//! 难度: Easy
//!
//! 算法: 异或运算（阿贝尔群性质）
//! 时间复杂度: O(n)
//! 空间复杂度: O(1)
//!
//! 数学基础: (B_32, ⊕) 构成阿贝尔群，满足交换律、结合律、自逆性（a ⊕ a = 0）。

pub struct Solution;

impl Solution {
    /// 找出数组中只出现一次的数字。
    ///
    /// 形式化规约:
    /// - 前置条件: 数组中恰好一个元素出现一次，其余均出现两次
    /// - 后置条件: 返回只出现一次的元素
    ///
    /// 核心性质: a ⊕ a = 0, a ⊕ 0 = a, a ⊕ b = b ⊕ a
    /// 因此所有元素异或后，成对元素抵消，剩余即为所求。
    pub fn single_number(nums: Vec<i32>) -> i32 {
        nums.iter().fold(0, |acc, &x| acc ^ x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_number_basic() {
        assert_eq!(Solution::single_number(vec![2, 2, 1]), 1);
    }

    #[test]
    fn test_single_number_multiple_pairs() {
        assert_eq!(Solution::single_number(vec![4, 1, 2, 1, 2]), 4);
    }

    #[test]
    fn test_single_number_single_element() {
        assert_eq!(Solution::single_number(vec![1]), 1);
    }
}
