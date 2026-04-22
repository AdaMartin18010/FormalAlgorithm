//! LeetCode 33. 搜索旋转排序数组
//!
//! 整数数组 nums 按升序排列，数组中的值互不相同。
//! 在传递给函数之前，nums 在预先未知的某个下标 k 处进行了旋转，
//! 使数组变为 [nums[k], nums[k+1], ..., nums[n-1], nums[0], ..., nums[k-1]]（下标从 0 开始）。
//! 给定旋转后的数组 nums 和一个整数 target，如果 nums 中存在这个目标值 target，则返回它的下标，否则返回 -1。
//!
//! 对标: LeetCode 33 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md

/// 在旋转排序数组中搜索目标值的索引。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为某个升序无重复数组经一次旋转所得，`len(nums) ∈ [0, 5000]`。
/// - **后置条件 (Post)**：若 `∃ i, nums[i] == target`，返回该索引 `i`；否则返回 `-1`。
///
/// # 循环不变式
///
/// 设当前搜索区间为闭区间 `[left, right]`：
/// > 若 `target` 存在于 `nums` 中，则其索引必然落在 `[left, right]` 范围内。
///
/// **维护**：
/// - 每次取 `mid`，数组被分为 `[left, mid]` 和 `[mid, right]`。
/// - 旋转数组有一个性质：至少有一半是有序的。
/// - 若 `nums[left] <= nums[mid]`，则左半部分 `[left, mid]` 有序：
///   - 当 `target` 落在该有序区间内（`nums[left] <= target < nums[mid]`），
///     可安全排除右半部分，令 `right = mid - 1`。
///   - 否则排除左半部分，令 `left = mid + 1`。
/// - 若 `nums[left] > nums[mid]`，则右半部分 `[mid, right]` 有序：
///   - 当 `target` 落在该有序区间内（`nums[mid] < target <= nums[right]`），
///     可安全排除左半部分，令 `left = mid + 1`。
///   - 否则排除右半部分，令 `right = mid - 1`。
/// - 以上操作保持区间仍包含可能的目标索引。
///
/// **终止推出**：当 `left > right` 时区间为空，由不变式知 `target` 不在数组中，返回 `-1`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n) — 每次迭代将搜索区间长度减半。
/// - **空间复杂度**：O(1) — 仅使用常数个额外变量。
///
/// # 证明要点
///
/// - 正确性依赖于「旋转排序数组中至少有一半是有序的」这一性质。
/// - 详细证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md`
/// - 终止性由区间长度严格递减保证。
pub fn search(nums: Vec<i32>, target: i32) -> i32 {
    if nums.is_empty() {
        return -1;
    }

    let mut left: i32 = 0;
    let mut right: i32 = nums.len() as i32 - 1;

    while left <= right {
        let mid = left + (right - left) / 2;
        let mid_val = nums[mid as usize];

        if mid_val == target {
            return mid;
        }

        let left_val = nums[left as usize];

        if left_val <= mid_val {
            // 左半部分有序
            if target >= left_val && target < mid_val {
                right = mid - 1;
            } else {
                left = mid + 1;
            }
        } else {
            // 右半部分有序
            let right_val = nums[right as usize];
            if target > mid_val && target <= right_val {
                left = mid + 1;
            } else {
                right = mid - 1;
            }
        }
    }

    -1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let nums = vec![4, 5, 6, 7, 0, 1, 2];
        assert_eq!(search(nums, 0), 4);
    }

    #[test]
    fn test_leetcode_example_2() {
        let nums = vec![4, 5, 6, 7, 0, 1, 2];
        assert_eq!(search(nums, 3), -1);
    }

    #[test]
    fn test_leetcode_example_3() {
        let nums = vec![1];
        assert_eq!(search(nums, 0), -1);
    }

    #[test]
    fn test_empty_array() {
        assert_eq!(search(vec![], 1), -1);
    }

    #[test]
    fn test_single_element_found() {
        assert_eq!(search(vec![5], 5), 0);
    }

    #[test]
    fn test_single_element_not_found() {
        assert_eq!(search(vec![5], 1), -1);
    }

    #[test]
    fn test_not_rotated() {
        let nums = vec![1, 2, 3, 4, 5];
        assert_eq!(search(nums.clone(), 3), 2);
        assert_eq!(search(nums, 6), -1);
    }

    #[test]
    fn test_target_at_rotation_point() {
        let nums = vec![3, 4, 5, 1, 2];
        assert_eq!(search(nums, 1), 3);
    }

    #[test]
    fn test_large_array() {
        let nums: Vec<i32> = (5000..10_000).chain(0..5000).collect();
        assert_eq!(search(nums.clone(), 7_500), 2_500);
        assert_eq!(search(nums, 10_001), -1);
    }
}
