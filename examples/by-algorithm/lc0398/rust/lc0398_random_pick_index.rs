//! LeetCode 398. 随机数索引
//!
//! 给定一个可能包含重复数字的整数数组，等概率随机返回目标数的索引。
//!
//! # Approach
//! 蓄水池抽样（Reservoir Sampling）：
//! 遍历数组，维护一个计数器 count 记录已遇到的目标数个数。
//! 当遇到第 k 个目标数时，以 1/k 的概率选择其索引作为当前结果。
//!
//! # Correctness Proof
//! 数学归纳法证明每个目标数索引被选择的概率均为 1/m（m 为目标数出现次数）：
//! - 基础：k=1 时，第一个目标数以概率 1 被选择，符合 1/1。
//! - 归纳：假设前 k-1 个目标数中每个被选择的概率均为 1/(k-1)。
//!   对于第 k 个目标数，以 1/k 概率选择它。
//!   对于前 k-1 个中的任意一个，它被保留的概率 = 之前被选中且第 k 次不替换它
//!   = (1/(k-1)) · ((k-1)/k) = 1/k。
//! - 终止时 k=m，每个目标数索引被选中的概率均为 1/m。
//!
//! # Complexity
//! - Time complexity: O(n) 每次 pick，n 为数组长度
//! - Space complexity: O(1)

use rand::Rng;

pub struct Solution {
    nums: Vec<i32>,
}

impl Solution {
    pub fn new(nums: Vec<i32>) -> Self {
        Solution { nums }
    }

    pub fn pick_index(&self, target: i32) -> i32 {
        let mut count = 0;
        let mut result = 0;
        let mut rng = rand::thread_rng();

        for (i, &num) in self.nums.iter().enumerate() {
            if num == target {
                count += 1;
                // 以 1/count 的概率选择当前索引
                if rng.gen_range(0..count) == 0 {
                    result = i as i32;
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_pick_index() {
        let sol = Solution::new(vec![1, 2, 3, 3, 3]);

        // 测试 target=3 时只返回索引 2,3,4
        for _ in 0..20 {
            let idx = sol.pick_index(3);
            assert!(idx == 2 || idx == 3 || idx == 4);
        }

        // 测试 target=1 时只返回索引 0
        assert_eq!(sol.pick_index(1), 0);

        // 测试 target=2 时只返回索引 1
        assert_eq!(sol.pick_index(2), 1);
    }

    #[test]
    fn test_distribution() {
        let sol = Solution::new(vec![1, 2, 3, 3, 3]);
        let mut freq = HashMap::new();
        let trials = 3000;

        for _ in 0..trials {
            let idx = sol.pick_index(3);
            *freq.entry(idx).or_insert(0) += 1;
        }

        // 每个索引的理论频率约为 1000，允许 30% 误差
        for &idx in &[2, 3, 4] {
            let count = freq.get(&idx).unwrap_or(&0);
            assert!(
                *count > 700 && *count < 1300,
                "Index {} frequency {} out of range",
                idx,
                count
            );
        }
    }
}
