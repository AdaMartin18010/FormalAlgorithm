//! LeetCode 45. 跳跃游戏 II
//!
//! 返回到达 nums[n - 1] 的最小跳跃次数。假设你总是可以到达 nums[n - 1]。
//!
//! 对标: LeetCode 45 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md

/// 计算到达最后一个位置的最小跳跃次数。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为非负整数数组，保证可以到达最后一个位置。
/// - **后置条件 (Post)**：返回从索引 0 到达索引 n-1 的最小跳跃次数。
///
/// # 核心思路
///
/// 贪心法（BFS 思想）：
/// - 维护当前层的最远边界 `current_end` 和下一层的最远边界 `farthest`。
/// - 当遍历到 `current_end` 时，必须再进行一次跳跃，将 `current_end` 更新为 `farthest`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n)` — 单次遍历。
/// - **空间复杂度**：`O(1)` — 仅使用常数额外变量。
pub fn jump(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut jumps = 0;
    let mut current_end = 0;
    let mut farthest = 0;

    for i in 0..n - 1 {
        farthest = farthest.max(i + nums[i] as usize);
        if i == current_end {
            jumps += 1;
            current_end = farthest;
            if current_end >= n - 1 {
                break;
            }
        }
    }

    jumps
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(jump(vec![2, 3, 1, 1, 4]), 2);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(jump(vec![2, 3, 0, 1, 4]), 2);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(jump(vec![0]), 0);
    }

    #[test]
    fn test_two_elements() {
        assert_eq!(jump(vec![1, 1]), 1);
    }

    #[test]
    fn test_all_ones() {
        assert_eq!(jump(vec![1, 1, 1, 1, 1]), 4);
    }
}
