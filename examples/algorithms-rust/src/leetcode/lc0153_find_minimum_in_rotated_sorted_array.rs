//! LeetCode 153. 寻找旋转排序数组中的最小值
//!
//! 已知一个长度为 n 的数组，预先按照升序排列，经由 1 到 n 次旋转后，得到输入数组。
//! 例如，原数组 nums = [0,1,2,4,5,6,7] 在变化后可能得到：
//! - 若旋转 4 次，则可以得到 [4,5,6,7,0,1,2]
//! - 若旋转 7 次，则可以得到 [0,1,2,4,5,6,7]
//! 注意，数组 [a[0], a[1], ..., a[n-1]] 旋转一次的结果为数组 [a[n-1], a[0], a[1], ..., a[n-2]] 。
//! 给你一个元素值互不相同的旋转数组 nums ，返回数组中的最小元素。
//!
//! 对标: LeetCode 153 / docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md

/// 寻找旋转排序数组中的最小值。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为某个升序无重复数组经若干次旋转所得，`len(nums) >= 1`。
/// - **后置条件 (Post)**：返回 `nums` 中最小元素的值，即 `min(nums)`。
///
/// # 循环不变式
///
/// 设当前搜索区间为闭区间 `[left, right]`：
/// > 最小元素始终位于 `[left, right]` 范围内。
///
/// **维护**：
/// - 初始时 `left = 0`，`right = n - 1`，不变式显然成立。
/// - 每次取 `mid = left + (right - left) / 2`：
///   - 若 `nums[mid] > nums[right]`，说明最小值在右半部分（旋转点右侧），
///     令 `left = mid + 1`。
///   - 若 `nums[mid] < nums[right]`，说明 `[mid, right]` 整体有序，
///     最小值在左半部分或就是 `mid`，令 `right = mid`。
///   - 因题目保证元素互不相同，不会出现 `nums[mid] == nums[right]`。
/// - 以上操作保持最小值仍在新区间内。
///
/// **终止推出**：当 `left == right` 时，区间仅含一个元素，由不变式知其即为最小值。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n) — 每次迭代将搜索区间长度减半。
/// - **空间复杂度**：O(1) — 仅使用常数个额外变量。
///
/// # 证明要点
///
/// - 关键性质：在旋转排序数组中，`nums[mid]` 与 `nums[right]` 的大小关系
///   唯一确定了最小值所在的半区。
/// - 详细证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md`
/// - 终止性由 `left < right` 条件及区间长度严格递减保证。
pub fn find_min(nums: Vec<i32>) -> i32 {
    let mut left = 0usize;
    let mut right = nums.len() - 1;

    while left < right {
        let mid = left + (right - left) / 2;

        if nums[mid] > nums[right] {
            left = mid + 1;
        } else {
            // nums[mid] < nums[right]，因元素互不相同
            right = mid;
        }
    }

    nums[left]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let nums = vec![3, 4, 5, 1, 2];
        assert_eq!(find_min(nums), 1);
    }

    #[test]
    fn test_leetcode_example_2() {
        let nums = vec![4, 5, 6, 7, 0, 1, 2];
        assert_eq!(find_min(nums), 0);
    }

    #[test]
    fn test_leetcode_example_3() {
        let nums = vec![11, 13, 15, 17];
        assert_eq!(find_min(nums), 11);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(find_min(vec![5]), 5);
    }

    #[test]
    fn test_two_elements_rotated() {
        assert_eq!(find_min(vec![2, 1]), 1);
    }

    #[test]
    fn test_two_elements_not_rotated() {
        assert_eq!(find_min(vec![1, 2]), 1);
    }

    #[test]
    fn test_not_rotated() {
        let nums = vec![1, 2, 3, 4, 5];
        assert_eq!(find_min(nums), 1);
    }

    #[test]
    fn test_large_array() {
        let nums: Vec<i32> = (5000..10_000).chain(0..5000).collect();
        assert_eq!(find_min(nums), 0);
    }

    #[test]
    fn test_target_at_rotation_point_end() {
        let nums = vec![2, 3, 4, 5, 1];
        assert_eq!(find_min(nums), 1);
    }
}
