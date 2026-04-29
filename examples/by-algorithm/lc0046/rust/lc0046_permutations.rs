//! LeetCode 46. Permutations
//! 链接: https://leetcode.com/problems/permutations/
//! 难度: Medium
//!
//! 算法: 回溯（排列树）
//! 时间复杂度: O(n * n!)
//! 空间复杂度: O(n)

pub struct Solution;

impl Solution {
    /// 生成 nums 的所有全排列。
    ///
    /// 形式化规约:
    /// - 前置条件: nums 为无重复元素的整数数组
    /// - 后置条件: 返回 nums 的所有 n! 个排列，无重复
    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let n = nums.len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut path: Vec<i32> = Vec::with_capacity(n);
        let mut used = vec![false; n];

        Self::backtrack(&nums, n, 0, &mut used, &mut path, &mut res);
        res
    }

    fn backtrack(
        nums: &[i32],
        n: usize,
        k: usize,
        used: &mut [bool],
        path: &mut Vec<i32>,
        res: &mut Vec<Vec<i32>>,
    ) {
        if k == n {
            // 找到一个完整解
            res.push(path.clone());
            return;
        }

        for i in 0..n {
            if used[i] {
                continue;
            }
            // 做选择
            used[i] = true;
            path.push(nums[i]);
            // 递归
            Self::backtrack(nums, n, k + 1, used, path, res);
            // 撤销选择
            path.pop();
            used[i] = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permute_3_elements() {
        let nums = vec![1, 2, 3];
        let res = Solution::permute(nums);
        assert_eq!(res.len(), 6);
    }

    #[test]
    fn test_permute_2_elements() {
        let nums = vec![0, 1];
        let res = Solution::permute(nums);
        assert_eq!(res.len(), 2);
    }

    #[test]
    fn test_permute_1_element() {
        let nums = vec![1];
        let res = Solution::permute(nums);
        assert_eq!(res, vec![vec![1]]);
    }
}
