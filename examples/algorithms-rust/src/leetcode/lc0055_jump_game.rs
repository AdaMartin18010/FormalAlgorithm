//! LeetCode 55. Jump Game
//! 链接: https://leetcode.com/problems/jump-game/
//! 难度: Medium
//!
//! 题目描述:
//! 给定一个非负整数数组 nums，你最初位于数组的第一个下标。
//! 数组中的每个元素代表你在该位置可以跳跃的最大长度。
//! 判断你是否能够到达最后一个下标。
//!
//! 形式化规约:
//!   输入: 数组 nums ∈ N^n，nums[i] 表示从位置 i 最多可跳跃的步数
//!   输出: 能否到达最后一个下标
//!
//! 最优解思路:
//!   贪心维护最远可达距离 max_reach。
//!   遍历每个位置，若当前位置 ≤ max_reach，则更新 max_reach = max(max_reach, i + nums[i])。
//!
//! 复杂度:
//!   时间: O(n)
//!   空间: O(1)
//!
//! 正确性要点 — 交换论证:
//!   贪心策略: 维护最远可达位置，若当前位置不可达则提前返回 false。
//!   证明: 假设存在某个最优解（某条可达路径），其每一步的位置序列为 p_0, p_1, ..., p_k。
//!   贪心策略维护的 max_reach 在每一步都不小于 p_i 所能到达的最远位置
//!   （因为 max_reach 取了所有前面位置的最大值）。
//!   因此若贪心策略无法到达位置 i，则没有任何路径能到达 i。
//!   反之，若贪心策略能到达终点，则必然存在可行路径。

pub struct Solution;

impl Solution {
    pub fn can_jump(nums: Vec<i32>) -> bool {
        let n = nums.len();
        if n <= 1 {
            return true;
        }

        let mut max_reach = 0usize;

        for i in 0..n {
            // 若当前位置已不可达，返回 false
            if i > max_reach {
                return false;
            }
            // 更新最远可达位置
            let reach = i + nums[i] as usize;
            if reach > max_reach {
                max_reach = reach;
            }
            // 提前退出：已可到达终点
            if max_reach >= n - 1 {
                return true;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(Solution::can_jump(vec![2, 3, 1, 1, 4]));
    }

    #[test]
    fn test_example_2() {
        assert!(!Solution::can_jump(vec![3, 2, 1, 0, 4]));
    }

    #[test]
    fn test_single_element() {
        assert!(Solution::can_jump(vec![0]));
    }

    #[test]
    fn test_all_zeros() {
        assert!(!Solution::can_jump(vec![0, 0, 0]));
    }

    #[test]
    fn test_large_jump() {
        assert!(Solution::can_jump(vec![5, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn test_just_reach() {
        assert!(Solution::can_jump(vec![1, 1, 1, 1]));
    }
}
