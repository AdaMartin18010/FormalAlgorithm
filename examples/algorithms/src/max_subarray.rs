//! 最大子数组问题（Maximum Subarray Problem）
//!
//! 给定一个整数数组，寻找具有最大和的连续子数组。
//! 本模块提供三种实现：
//! - 暴力法：O(n²)
//! - 分治法：O(n log n)
//! - Kadane 动态规划：O(n)
//!
//! 对标：CLRS Chapter 4.1

/// 暴力法求解最大子数组
///
/// # 时间复杂度
/// - O(n²)
pub fn max_subarray_brute_force(arr: &[i64]) -> Option<(usize, usize, i64)> {
    if arr.is_empty() {
        return None;
    }

    let mut max_sum = arr[0];
    let mut left = 0;
    let mut right = 0;

    for i in 0..arr.len() {
        let mut sum = 0;
        for j in i..arr.len() {
            sum += arr[j];
            if sum > max_sum {
                max_sum = sum;
                left = i;
                right = j;
            }
        }
    }

    Some((left, right, max_sum))
}

/// 分治法求解最大子数组
///
/// # 时间复杂度
/// - O(n log n)
///
/// # 示例
/// ```
/// use formal_algorithms::max_subarray::max_subarray_divide_and_conquer;
///
/// let arr = vec![13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7];
/// let (l, r, sum) = max_subarray_divide_and_conquer(&arr).unwrap();
/// assert_eq!((l, r, sum), (7, 10, 43));
/// ```
pub fn max_subarray_divide_and_conquer(arr: &[i64]) -> Option<(usize, usize, i64)> {
    if arr.is_empty() {
        return None;
    }
    Some(max_subarray_recursive(arr, 0, arr.len() - 1))
}

fn max_subarray_recursive(arr: &[i64], low: usize, high: usize) -> (usize, usize, i64) {
    if low == high {
        return (low, high, arr[low]);
    }

    let mid = low + (high - low) / 2;
    let (left_low, left_high, left_sum) = max_subarray_recursive(arr, low, mid);
    let (right_low, right_high, right_sum) = max_subarray_recursive(arr, mid + 1, high);
    let (cross_low, cross_high, cross_sum) = max_crossing_subarray(arr, low, mid, high);

    if left_sum >= right_sum && left_sum >= cross_sum {
        (left_low, left_high, left_sum)
    } else if right_sum >= left_sum && right_sum >= cross_sum {
        (right_low, right_high, right_sum)
    } else {
        (cross_low, cross_high, cross_sum)
    }
}

fn max_crossing_subarray(arr: &[i64], low: usize, mid: usize, high: usize) -> (usize, usize, i64) {
    let mut left_sum = i64::MIN;
    let mut sum = 0i64;
    let mut max_left = mid;

    for i in (low..=mid).rev() {
        sum += arr[i];
        if sum > left_sum {
            left_sum = sum;
            max_left = i;
        }
    }

    let mut right_sum = i64::MIN;
    sum = 0;
    let mut max_right = mid + 1;

    for j in (mid + 1)..=high {
        sum += arr[j];
        if sum > right_sum {
            right_sum = sum;
            max_right = j;
        }
    }

    (max_left, max_right, left_sum + right_sum)
}

/// Kadane 算法（动态规划）求解最大子数组
///
/// # 时间复杂度
/// - O(n)
///
/// # 示例
/// ```
/// use formal_algorithms::max_subarray::max_subarray_kadane;
///
/// let arr = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
/// let (l, r, sum) = max_subarray_kadane(&arr).unwrap();
/// assert_eq!(sum, 6); // [4, -1, 2, 1]
/// ```
pub fn max_subarray_kadane(arr: &[i64]) -> Option<(usize, usize, i64)> {
    if arr.is_empty() {
        return None;
    }

    let mut max_sum = arr[0];
    let mut current_sum = arr[0];
    let mut max_left = 0;
    let mut max_right = 0;
    let mut current_left = 0;

    for i in 1..arr.len() {
        if current_sum < 0 {
            current_sum = arr[i];
            current_left = i;
        } else {
            current_sum += arr[i];
        }

        if current_sum > max_sum {
            max_sum = current_sum;
            max_left = current_left;
            max_right = i;
        }
    }

    Some((max_left, max_right, max_sum))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_brute_force() {
        let arr = vec![13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7];
        let (l, r, sum) = max_subarray_brute_force(&arr).unwrap();
        assert_eq!((l, r, sum), (7, 10, 43));
    }

    #[test]
    fn test_divide_and_conquer() {
        let arr = vec![13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7];
        let (l, r, sum) = max_subarray_divide_and_conquer(&arr).unwrap();
        assert_eq!((l, r, sum), (7, 10, 43));
    }

    #[test]
    fn test_kadane() {
        let arr = vec![13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7];
        let (l, r, sum) = max_subarray_kadane(&arr).unwrap();
        assert_eq!((l, r, sum), (7, 10, 43));
    }

    #[test]
    fn test_all_negative() {
        let arr = vec![-5, -2, -8, -1, -9];
        let (_, _, sum) = max_subarray_kadane(&arr).unwrap();
        assert_eq!(sum, -1);
    }

    #[test]
    fn test_single_element() {
        let arr = vec![42];
        assert_eq!(max_subarray_kadane(&arr), Some((0, 0, 42)));
    }

    #[test]
    fn test_empty() {
        let arr: Vec<i64> = vec![];
        assert_eq!(max_subarray_kadane(&arr), None);
    }
}
