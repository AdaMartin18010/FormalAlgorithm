//! LeetCode 4. 寻找两个正序数组的中位数
//!
//! 给定两个大小分别为 m 和 n 的正序数组，找出并返回这两个正序数组的中位数。
//! 算法的时间复杂度应该为 O(log (m+n))。
//!
//! 对标: LeetCode 4 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md

/// 寻找两个正序数组的中位数。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums1` 和 `nums2` 各自按非降序排列；`m + n >= 1`。
/// - **后置条件 (Post)**：返回两个数组合并后的中位数。
///
/// # 核心思路
///
/// 二分/分治混合：在较短的数组上进行二分查找分割点。
/// 设将 `nums1` 在位置 `i` 处分割，`nums2` 在位置 `j` 处分割，满足 `i + j = (m + n + 1) / 2`。
/// 要求：`nums1[i-1] <= nums2[j]` 且 `nums2[j-1] <= nums1[i]`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(log(min(m, n)))`
/// - **空间复杂度**：`O(1)`
pub fn find_median_sorted_arrays(nums1: Vec<i32>, nums2: Vec<i32>) -> f64 {
    // 确保 nums1 是较短的数组
    let (nums1, nums2) = if nums1.len() > nums2.len() {
        (nums2, nums1)
    } else {
        (nums1, nums2)
    };

    let m = nums1.len();
    let n = nums2.len();
    let total_left = (m + n + 1) / 2;

    let (mut left, mut right) = (0, m);
    while left <= right {
        let i = left + (right - left) / 2;
        let j = total_left - i;

        let nums1_left_max = if i == 0 {
            i32::MIN as f64
        } else {
            nums1[i - 1] as f64
        };
        let nums1_right_min = if i == m {
            i32::MAX as f64
        } else {
            nums1[i] as f64
        };

        let nums2_left_max = if j == 0 {
            i32::MIN as f64
        } else {
            nums2[j - 1] as f64
        };
        let nums2_right_min = if j == n {
            i32::MAX as f64
        } else {
            nums2[j] as f64
        };

        if nums1_left_max <= nums2_right_min && nums2_left_max <= nums1_right_min {
            if (m + n) % 2 == 1 {
                return nums1_left_max.max(nums2_left_max);
            } else {
                return (nums1_left_max.max(nums2_left_max) + nums1_right_min.min(nums2_right_min))
                    / 2.0;
            }
        } else if nums1_left_max > nums2_right_min {
            right = i - 1;
        } else {
            left = i + 1;
        }
    }

    0.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(find_median_sorted_arrays(vec![1, 3], vec![2]), 2.0);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(find_median_sorted_arrays(vec![1, 2], vec![3, 4]), 2.5);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(find_median_sorted_arrays(vec![], vec![1]), 1.0);
        assert_eq!(find_median_sorted_arrays(vec![2], vec![]), 2.0);
    }

    #[test]
    fn test_interleaved() {
        assert_eq!(find_median_sorted_arrays(vec![1, 2, 3], vec![4, 5, 6]), 3.5);
    }
}
