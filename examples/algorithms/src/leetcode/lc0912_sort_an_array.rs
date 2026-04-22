//! LeetCode 912. 排序数组
//!
//! 使用归并排序将数组升序排列。
//!
//! 对标: LeetCode 912 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md

/// 使用归并排序将数组升序排列。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为整数数组。
/// - **后置条件 (Post)**：返回 `nums` 的一个非降序排列（元素多重集相同）。
///
/// # 核心思路
///
/// 分治归并排序：
/// 1. 分解：将数组从中间分为两半。
/// 2. 解决：递归对左右两半分别排序。
/// 3. 合并：将两个已排序的子数组合并为一个有序数组。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n log n)` — 递归树深度 `log n`，每层合并 `O(n)`。
/// - **空间复杂度**：`O(n)` — 合并过程需要辅助数组。
pub fn sort_array(nums: Vec<i32>) -> Vec<i32> {
    let n = nums.len();
    if n <= 1 {
        return nums;
    }

    let mid = n / 2;
    let left = sort_array(nums[..mid].to_vec());
    let right = sort_array(nums[mid..].to_vec());

    merge(&left, &right)
}

fn merge(left: &[i32], right: &[i32]) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }

    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(sort_array(vec![5, 2, 3, 1]), vec![1, 2, 3, 5]);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(sort_array(vec![5, 1, 1, 2, 0, 0]), vec![0, 0, 1, 1, 2, 5]);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(sort_array(vec![1]), vec![1]);
    }

    #[test]
    fn test_all_same() {
        assert_eq!(sort_array(vec![3, 3, 3]), vec![3, 3, 3]);
    }
}
