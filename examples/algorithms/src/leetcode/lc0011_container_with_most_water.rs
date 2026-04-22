//! LeetCode 11. 盛最多水的容器
//!
//! 给定一个长度为 n 的整数数组 height。有 n 条垂线，第 i 条线的两个端点是 (i, 0) 和 (i, height[i])。
//! 找出其中的两条线，使得它们与 x 轴共同构成的容器可以容纳最多的水。
//!
//! 对标: LeetCode 11 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

/// 计算能容纳最多水的容器面积。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`height` 长度范围 `[2, 10^5]`，元素范围 `[0, 10^4]`。
/// - **后置条件 (Post)**：返回 `max_{i < j} min(height[i], height[j]) * (j - i)`。
///
/// # 核心思路
///
/// 双指针法：初始化 `left = 0`, `right = n - 1`。
/// 当前面积由较短的板决定。向内移动较长的板面积不可能增大，因此移动较短的板。
///
/// # 循环不变式
///
/// 已遍历的所有以 `l' < left` 或 `r' > right` 为边界的容器面积均已考察过。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 双指针各移动至多 n 次。
/// - **空间复杂度**：O(1) — 仅使用常数个额外变量。
///
/// # 证明要点
///
/// 对于状态 `(l, r)`，设 `height[l] <= height[r]`。
/// 对于任何 `k ∈ (l, r)`，`area(l, k) <= height[l] * (k-l) < height[l] * (r-l) = area(l, r)`。
/// 因此可以安全地排除 `l` 而不遗漏最优解。
pub fn max_area(height: Vec<i32>) -> i32 {
    let mut left: usize = 0;
    let mut right: usize = height.len() - 1;
    let mut best: i32 = 0;

    while left < right {
        let width = (right - left) as i32;
        if height[left] < height[right] {
            best = best.max(height[left] * width);
            left += 1;
        } else {
            best = best.max(height[right] * width);
            right -= 1;
        }
    }

    best
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(max_area(vec![1, 8, 6, 2, 5, 4, 8, 3, 7]), 49);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(max_area(vec![1, 1]), 1);
    }

    #[test]
    fn test_all_zeros() {
        assert_eq!(max_area(vec![0, 0]), 0);
    }

    #[test]
    fn test_increasing() {
        assert_eq!(max_area(vec![1, 2, 3, 4, 5]), 6);
    }

    #[test]
    fn test_decreasing() {
        assert_eq!(max_area(vec![5, 4, 3, 2, 1]), 6);
    }
}
