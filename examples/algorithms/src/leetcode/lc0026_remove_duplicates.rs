//! LeetCode 26. 删除有序数组中的重复项
//!
//! 给你一个 非严格递增排列 的数组 nums ，请你 原地 删除重复出现的元素，
//! 使每个元素 只出现一次 ，返回删除后数组的新长度。元素的 相对顺序 应该保持 一致 。
//!
//! 对标: LeetCode 26 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

/// 原地删除有序数组中的重复项，返回去重后的长度。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 已按非严格递增排序。
/// - **后置条件 (Post)**：返回 `k` 满足 `nums[0..k]` 为严格递增（无重复），
///   且 `nums[0..k]` 恰好包含原数组中所有不同元素各一次，保持相对顺序。
///
/// # 核心思路
///
/// 双指针（快慢指针）：
/// - `slow` 指向已去重区域的下一个待写入位置（即去重后数组的末尾+1）。
/// - `fast` 遍历整个数组寻找下一个与去重区域末尾不同的元素。
///
/// 初始时 `slow = 1`，因为第一个元素必然保留。
/// 当 `nums[fast] != nums[slow - 1]` 时，将 `nums[fast]` 复制到 `nums[slow]`，
/// 然后 `slow += 1`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 单次遍历数组。
/// - **空间复杂度**：O(1) — 仅使用常数额外空间，原地修改。
///
/// # 证明要点
///
/// - 循环不变式：每次迭代开始时，`nums[0..slow]` 已去重且保持相对顺序，
///   且 `nums[slow - 1]` 为当前已处理元素中的最大值。
/// - 终止时 `fast == n`，所有元素已处理，`nums[0..slow]` 即为所求。
pub fn remove_duplicates(nums: &mut Vec<i32>) -> i32 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut slow = 1;
    for fast in 1..n {
        if nums[fast] != nums[slow - 1] {
            nums[slow] = nums[fast];
            slow += 1;
        }
    }
    slow as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let mut nums = vec![1, 1, 2];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 2);
        assert_eq!(&nums[..k as usize], &[1, 2]);
    }

    #[test]
    fn test_example_2() {
        let mut nums = vec![0, 0, 1, 1, 1, 2, 2, 3, 3, 4];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 5);
        assert_eq!(&nums[..k as usize], &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_empty() {
        let mut nums: Vec<i32> = vec![];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 0);
    }

    #[test]
    fn test_single_element() {
        let mut nums = vec![5];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 1);
        assert_eq!(&nums[..k as usize], &[5]);
    }

    #[test]
    fn test_all_distinct() {
        let mut nums = vec![1, 2, 3, 4, 5];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 5);
        assert_eq!(&nums[..k as usize], &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_all_same() {
        let mut nums = vec![2, 2, 2, 2, 2];
        let k = remove_duplicates(&mut nums);
        assert_eq!(k, 1);
        assert_eq!(&nums[..k as usize], &[2]);
    }
}
