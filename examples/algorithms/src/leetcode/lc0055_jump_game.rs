//! LeetCode 55. 跳跃游戏
//!
//! 判断是否能到达数组的最后一个下标。
//!
//! 对标: LeetCode 55 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md

/// 判断是否能到达最后一个下标。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为非负整数数组。
/// - **后置条件 (Post)**：若能从位置 0 到达位置 n-1，返回 `true`。
///
/// # 核心思路
///
/// 贪心策略：维护最远可达位置 `reach`。
/// 若当前位置 `i <= reach`，则更新 `reach = max(reach, i + nums[i])`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n)`
/// - **空间复杂度**：`O(1)`
pub fn can_jump(nums: Vec<i32>) -> bool {
    let n = nums.len();
    let mut reach = 0;

    for i in 0..n {
        if i > reach {
            return false;
        }
        reach = reach.max(i + nums[i] as usize);
        if reach >= n - 1 {
            return true;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(can_jump(vec![2, 3, 1, 1, 4]));
    }

    #[test]
    fn test_example_2() {
        assert!(!can_jump(vec![3, 2, 1, 0, 4]));
    }

    #[test]
    fn test_single_element() {
        assert!(can_jump(vec![0]));
    }

    #[test]
    fn test_one_big_jump() {
        assert!(can_jump(vec![5, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn test_unreachable() {
        assert!(!can_jump(vec![0, 1]));
    }
}
