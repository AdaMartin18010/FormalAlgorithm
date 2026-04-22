//! LeetCode 435. 无重叠区间
//!
//! 找到需要移除区间的最小数量，使剩余区间互不重叠。
//!
//! 对标: LeetCode 435 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md

/// 计算需要移除的最小区间数量，使剩余区间互不重叠。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`intervals` 为区间集合。
/// - **后置条件 (Post)**：返回需要移除的最小区间数量。
///
/// # 核心思路
///
/// 贪心策略：按结束时间排序，每次选择结束最早的且与已选区间不重叠的区间。
/// 结束越早的区间，留给后续区间的空间越大。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n log n)` — 排序主导。
/// - **空间复杂度**：`O(1)` — 忽略排序栈空间。
pub fn erase_overlap_intervals(mut intervals: Vec<Vec<i32>>) -> i32 {
    let n = intervals.len();
    if n == 0 {
        return 0;
    }

    intervals.sort_by(|a, b| a[1].cmp(&b[1]));

    let mut count = 1;
    let mut end = intervals[0][1];

    for i in 1..n {
        if intervals[i][0] >= end {
            count += 1;
            end = intervals[i][1];
        }
    }

    (n - count) as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(
            erase_overlap_intervals(vec![vec![1, 2], vec![2, 3], vec![3, 4], vec![1, 3]]),
            1
        );
    }

    #[test]
    fn test_example_2() {
        assert_eq!(
            erase_overlap_intervals(vec![vec![1, 2], vec![1, 2], vec![1, 2]]),
            2
        );
    }

    #[test]
    fn test_example_3() {
        assert_eq!(
            erase_overlap_intervals(vec![vec![1, 2], vec![2, 3]]),
            0
        );
    }

    #[test]
    fn test_empty() {
        assert_eq!(erase_overlap_intervals(vec![]), 0);
    }

    #[test]
    fn test_one_big() {
        assert_eq!(
            erase_overlap_intervals(vec![vec![1, 10], vec![2, 3], vec![4, 5], vec![6, 7]]),
            1
        );
    }
}
