//! LeetCode 384. 打乱数组
//!
//! 实现 Fisher-Yates 洗牌算法，支持 reset 和 shuffle 操作。
//!
//! # Approach
//! - 结构体保存原始数组和当前数组。
//! - reset：返回原始数组的副本。
//! - shuffle：使用 Fisher-Yates 洗牌算法，从后往前遍历，
//!   对每个位置 i，从 [0, i] 中随机选择一个位置 j 并交换 nums[i] 和 nums[j]。
//!
//! # Correctness Proof
//! Fisher-Yates 洗牌算法的均匀性：
//! - 第 i 步（从 n-1 递减到 0），从 [0, i] 中均匀随机选择 j。
//! - 元素 nums[i] 被放到位置 j 后不再移动。
//! - 每个元素最终出现在每个位置的概率均为 1/n。
//!
//! # Complexity
//! - Time complexity: O(n) for shuffle, O(n) for reset
//! - Space complexity: O(n)

use rand::Rng;

pub struct Solution {
    nums: Vec<i32>,
    original: Vec<i32>,
}

impl Solution {
    pub fn new(nums: Vec<i32>) -> Self {
        Solution {
            original: nums.clone(),
            nums,
        }
    }

    pub fn reset(&self) -> Vec<i32> {
        self.original.clone()
    }

    pub fn shuffle(&mut self) -> Vec<i32> {
        let n = self.nums.len();
        let mut rng = rand::thread_rng();
        for i in (1..n).rev() {
            let j = rng.gen_range(0..=i);
            self.nums.swap(i, j);
        }
        self.nums.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shuffle_and_reset() {
        let nums = vec![1, 2, 3];
        let mut sol = Solution::new(nums.clone());

        let shuffled = sol.shuffle();
        let mut shuffled_sorted = shuffled.clone();
        shuffled_sorted.sort();
        assert_eq!(shuffled_sorted, vec![1, 2, 3]); // 元素一致

        assert_eq!(sol.reset(), vec![1, 2, 3]);
    }

    #[test]
    fn test_empty_and_single() {
        let sol = Solution::new(vec![]);
        assert_eq!(sol.reset(), vec![]);

        let mut sol2 = Solution::new(vec![5]);
        assert_eq!(sol2.shuffle(), vec![5]);
        assert_eq!(sol2.reset(), vec![5]);
    }
}
