//! LeetCode 455. 分发饼干
//!
//! 尽可能满足最多数量的孩子。
//!
//! 对标: LeetCode 455 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md

/// 计算最多能满足的孩子数量。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`g` 为孩子胃口值数组，`s` 为饼干尺寸数组。
/// - **后置条件 (Post)**：返回能满足的孩子的最大数量。
///
/// # 核心思路
///
/// 贪心策略：排序后双指针，用最小满足饼干满足每个孩子。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(m log m + n log n)` — 排序主导。
/// - **空间复杂度**：`O(1)` — 忽略排序栈空间。
pub fn find_content_children(mut g: Vec<i32>, mut s: Vec<i32>) -> i32 {
    g.sort_unstable();
    s.sort_unstable();

    let (mut child, mut cookie) = (0, 0);
    while child < g.len() && cookie < s.len() {
        if s[cookie] >= g[child] {
            child += 1;
        }
        cookie += 1;
    }

    child as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(find_content_children(vec![1, 2, 3], vec![1, 1]), 1);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(find_content_children(vec![1, 2], vec![1, 2, 3]), 2);
    }

    #[test]
    fn test_all_satisfy() {
        assert_eq!(find_content_children(vec![1, 2, 3], vec![3, 3, 3]), 3);
    }

    #[test]
    fn test_no_match() {
        assert_eq!(find_content_children(vec![2], vec![1]), 0);
    }
}
