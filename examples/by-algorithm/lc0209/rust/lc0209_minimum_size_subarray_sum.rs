//! LeetCode 209. 长度最小的子数组
//!
//! 给定一个含有 n 个正整数的数组 nums 和一个正整数 target，
//! 找出该数组中满足其和 ≥ target 的长度最小的连续子数组，并返回其长度。
//! 如果不存在符合条件的子数组，返回 0。
//!
//! # Approach
//! 滑动窗口（双指针）：维护窗口 [left, right] 的和 window_sum。
//! 当 window_sum ≥ target 时，尝试收缩 left 以寻找更短子数组。
//!
//! # Correctness Proof
//! 不变式：window_sum = sum(nums[left..right])。
//! - 扩展 right：window_sum += nums[right]，保持不变式。
//! - 当 window_sum ≥ target 时，当前窗口是一个可行解，更新最小长度。
//!   然后收缩 left：window_sum -= nums[left]，left += 1。
//!   由于 nums 中的元素都是正整数，收缩只会让窗口和减小或不变，
//!   因此一旦 window_sum < target，必须继续扩展 right 才能再次达到 target。
//! - 每个元素最多被加入窗口一次、移出窗口一次。
//!
//! # Complexity
//! - Time complexity: O(n)
//! - Space complexity: O(1)

pub fn min_sub_array_len(target: i32, nums: Vec<i32>) -> i32 {
    let n = nums.len();
    let mut min_len = n + 1;
    let mut left = 0;
    let mut window_sum = 0i64; // 使用 i64 防止溢出

    let t = target as i64;
    for right in 0..n {
        window_sum += nums[right] as i64;
        while window_sum >= t {
            let window_len = right - left + 1;
            if window_len < min_len {
                min_len = window_len;
            }
            window_sum -= nums[left] as i64;
            left += 1;
        }
    }

    if min_len == n + 1 {
        0
    } else {
        min_len as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(min_sub_array_len(7, vec![2, 3, 1, 2, 4, 3]), 2);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(min_sub_array_len(4, vec![1, 4, 4]), 1);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(min_sub_array_len(11, vec![1, 1, 1, 1, 1, 1, 1, 1]), 0);
    }

    #[test]
    fn test_single_element_exact() {
        assert_eq!(min_sub_array_len(5, vec![5]), 1);
    }

    #[test]
    fn test_single_element_insufficient() {
        assert_eq!(min_sub_array_len(5, vec![3]), 0);
    }

    #[test]
    fn test_whole_array_exact() {
        assert_eq!(min_sub_array_len(10, vec![1, 2, 3, 4]), 4);
    }

    #[test]
    fn test_large_array() {
        let large = vec![1; 100000];
        assert_eq!(min_sub_array_len(100000, large.clone()), 100000);
        assert_eq!(min_sub_array_len(50000, large), 50000);
    }
}
