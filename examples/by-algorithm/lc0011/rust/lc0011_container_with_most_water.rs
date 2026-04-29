//! LeetCode 11. Container With Most Water
//! 链接: https://leetcode.com/problems/container-with-most-water/
//! 难度: Medium
//!
//! 题目描述:
//! 给定一个长度为 n 的整数数组 height。有 n 条垂线，第 i 条线的两个端点是 (i, 0) 和 (i, height[i])。
//! 找出其中的两条线，使得它们与 x 轴共同构成的容器可以容纳最多的水。
//! 返回容器可以储存的最大水量。
//!
//! 形式化规约:
//!   输入: height ∈ N^n
//!   输出: max_{0 ≤ l < r < n} min(height[l], height[r]) × (r - l)
//!
//! 最优解思路:
//!   对撞双指针：初始化 l = 0, r = n - 1。
//!   每次移动高度较小的指针（因为移动高度较大的指针不可能增加面积）。
//!
//! 复杂度:
//!   时间: O(n)
//!   空间: O(1)
//!
//! 正确性要点:
//!   移动策略的正确性：设当前面积为 S = min(h[l], h[r]) × (r - l)。
//!   若 h[l] < h[r]，则对于任意 l' > l，以 l 为左端点、任意 r' < r 为右端点的面积都不会超过当前 S。
//!   因此可以安全地舍弃 l，移动左指针。

pub struct Solution;

impl Solution {
    pub fn max_area(height: Vec<i32>) -> i32 {
        let mut left = 0usize;
        let mut right = height.len() - 1;
        let mut max_area = 0i32;

        while left < right {
            let width = (right - left) as i32;
            let h = if height[left] < height[right] {
                height[left]
            } else {
                height[right]
            };
            let area = width * h;
            if area > max_area {
                max_area = area;
            }

            // 移动高度较小的一侧指针
            if height[left] < height[right] {
                left += 1;
            } else {
                right -= 1;
            }
        }

        max_area
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let height = vec![1, 8, 6, 2, 5, 4, 8, 3, 7];
        assert_eq!(Solution::max_area(height), 49);
    }

    #[test]
    fn test_example_2() {
        let height = vec![1, 1];
        assert_eq!(Solution::max_area(height), 1);
    }

    #[test]
    fn test_single_peak() {
        let height = vec![1, 2, 4, 3];
        assert_eq!(Solution::max_area(height), 4);
    }

    #[test]
    fn test_descending() {
        let height = vec![5, 4, 3, 2, 1];
        assert_eq!(Solution::max_area(height), 6); // 5 and 1 at ends: min(5,1)*4 = 4, best is index0&3: min(5,2)*3=6
    }
}
