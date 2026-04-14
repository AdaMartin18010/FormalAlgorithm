//! 快速选择与中位数算法实现
//!
//! 提供 QuickSelect 和 Median of Medians 两种线性时间选择算法。
//! 用于查找数组中第 k 小（或第 k 大）的元素。

use crate::{AlgorithmError, SearchResult};

/// QuickSelect - 查找第 k 小的元素（0-based 索引）
///
/// 平均时间复杂度 O(n)，最坏情况 O(n²)。
/// 该实现会修改输入数组。
///
/// # 算法说明
///
/// 1. 使用快速排序的分区思想，选择一个 pivot
/// 2. 根据 pivot 的最终位置决定递归方向
/// 3. 只需递归处理包含目标元素的那一半
///
/// # 复杂度分析
///
/// - **期望时间复杂度**: O(n)
/// - **最坏时间复杂度**: O(n²)
/// - **空间复杂度**: O(1) 辅助空间（不计递归栈 O(log n) 期望）
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_select;
///
/// let mut data = vec![7, 10, 4, 3, 20, 15];
/// let kth = quick_select(&mut data, 3).unwrap(); // 第4小的元素
/// assert_eq!(*kth, 10);
/// ```
///
/// # 错误
///
/// 若 k >= arr.len()，返回 `AlgorithmError::IndexOutOfBounds`。
pub fn quick_select<T: Ord>(arr: &mut [T], k: usize) -> SearchResult<&T> {
    if k >= arr.len() {
        return Err(AlgorithmError::IndexOutOfBounds {
            index: k,
            len: arr.len(),
        });
    }

    let idx = quick_select_internal(arr, k);
    Ok(&arr[idx])
}

fn quick_select_internal<T: Ord>(arr: &mut [T], k: usize) -> usize {
    if arr.len() == 1 {
        return 0;
    }

    let pivot_index = partition(arr);

    match k.cmp(&pivot_index) {
        std::cmp::Ordering::Equal => pivot_index,
        std::cmp::Ordering::Less => quick_select_internal(&mut arr[..pivot_index], k),
        std::cmp::Ordering::Greater => {
            let right_start = pivot_index + 1;
            let right_idx = quick_select_internal(&mut arr[right_start..], k - right_start);
            right_start + right_idx
        }
    }
}

/// 三数取中分区方案
fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let mid = len / 2;
    let last = len - 1;

    // 三数取中，将中位数放到 last 位置
    if arr[mid] < arr[0] {
        arr.swap(0, mid);
    }
    if arr[last] < arr[0] {
        arr.swap(0, last);
    }
    if arr[mid] < arr[last] {
        arr.swap(mid, last);
    }

    let mut i = 0;
    for j in 0..last {
        if arr[j] <= arr[last] {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, last);
    i
}

/// Median of Medians - 确定性线性时间选择
///
/// 最坏情况下时间复杂度为 O(n)，但常数因子较大。
/// 主要用于理论研究，实际工程中更常用 QuickSelect 或 IntroSelect。
///
/// # 算法说明
///
/// 1. 将数组分成每组 5 个元素的子组
/// 2. 找出每组的中位数
/// 3. 递归找出中位数的中位数作为 pivot
/// 4. 用该 pivot 分区，保证至少 30% 的元素被排除
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_select::median_of_medians_select;
///
/// let mut data = vec![7, 10, 4, 3, 20, 15, 1, 8, 12];
/// let kth = median_of_medians_select(&mut data, 3).unwrap();
/// assert_eq!(*kth, 7);
/// ```
pub fn median_of_medians_select<T: Ord + Clone>(arr: &mut [T], k: usize) -> SearchResult<&T> {
    if k >= arr.len() {
        return Err(AlgorithmError::IndexOutOfBounds {
            index: k,
            len: arr.len(),
        });
    }

    let idx = mom_select_internal(arr, k);
    Ok(&arr[idx])
}

fn mom_select_internal<T: Ord + Clone>(arr: &mut [T], k: usize) -> usize {
    if arr.len() <= 5 {
        arr.sort();
        return k;
    }

    // 1. 分成每组 5 个，找出中位数
    let mut medians = Vec::with_capacity((arr.len() + 4) / 5);
    let n = arr.len();
    for i in (0..n).step_by(5) {
        let end = (i + 5).min(n);
        arr[i..end].sort();
        let median_idx = i + (end - i) / 2;
        // 安全地取出中位数
        medians.push(arr[median_idx].clone());
    }

    // 2. 递归找出中位数的中位数
    let median_idx = medians.len() / 2;
    let median_of_median_idx = mom_select_internal(&mut medians, median_idx);
    let pivot = medians[median_of_median_idx].clone();

    // 3. 用 pivot 分区
    let pivot_idx = partition_by_value(arr, &pivot);

    match k.cmp(&pivot_idx) {
        std::cmp::Ordering::Equal => pivot_idx,
        std::cmp::Ordering::Less => mom_select_internal(&mut arr[..pivot_idx], k),
        std::cmp::Ordering::Greater => {
            let right_start = pivot_idx + 1;
            let right_idx = mom_select_internal(&mut arr[right_start..], k - right_start);
            right_start + right_idx
        }
    }
}

/// 按给定值分区，返回等于该值的某个位置
fn partition_by_value<T: Ord>(arr: &mut [T], pivot: &T) -> usize {
    let mut lt = 0;
    let mut gt = arr.len();
    let mut i = 0;

    while i < gt {
        if arr[i] < *pivot {
            arr.swap(lt, i);
            lt += 1;
            i += 1;
        } else if arr[i] > *pivot {
            gt -= 1;
            arr.swap(i, gt);
        } else {
            i += 1;
        }
    }

    // 返回第一个等于 pivot 的位置
    lt
}

/// 查找中位数
///
/// 若数组长度为偶数，返回下中位数（第 n/2 小的元素，0-based）。
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_select::find_median;
///
/// let mut data = vec![7, 10, 4, 3, 20];
/// let median = find_median(&mut data).unwrap();
/// assert_eq!(*median, 7);
/// ```
pub fn find_median<T: Ord>(arr: &mut [T]) -> SearchResult<&T> {
    let k = arr.len() / 2;
    quick_select(arr, k)
}

/// 查找最大值
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_select::find_max;
///
/// let mut data = vec![7, 10, 4, 3, 20];
/// let max = find_max(&mut data).unwrap();
/// assert_eq!(*max, 20);
/// ```
pub fn find_max<T: Ord>(arr: &mut [T]) -> SearchResult<&T> {
    if arr.is_empty() {
        return Err(AlgorithmError::InvalidInput("Empty array".to_string()));
    }
    quick_select(arr, arr.len() - 1)
}

/// 查找最小值
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_select::find_min;
///
/// let mut data = vec![7, 10, 4, 3, 20];
/// let min = find_min(&mut data).unwrap();
/// assert_eq!(*min, 3);
/// ```
pub fn find_min<T: Ord>(arr: &mut [T]) -> SearchResult<&T> {
    if arr.is_empty() {
        return Err(AlgorithmError::InvalidInput("Empty array".to_string()));
    }
    quick_select(arr, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quick_select_basic() {
        let mut arr = vec![7, 10, 4, 3, 20, 15];
        assert_eq!(*quick_select(&mut arr, 0).unwrap(), 3);
        assert_eq!(*quick_select(&mut arr, 2).unwrap(), 7);
        assert_eq!(*quick_select(&mut arr, 5).unwrap(), 20);
    }

    #[test]
    fn test_quick_select_single() {
        let mut arr = vec![42];
        assert_eq!(*quick_select(&mut arr, 0).unwrap(), 42);
    }

    #[test]
    fn test_quick_select_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        assert_eq!(*quick_select(&mut arr, 0).unwrap(), 1);
        assert_eq!(*quick_select(&mut arr, 9).unwrap(), 9);
    }

    #[test]
    fn test_quick_select_error() {
        let mut arr = vec![1, 2, 3];
        assert!(quick_select(&mut arr, 10).is_err());
    }

    #[test]
    fn test_median_of_medians() {
        let mut arr = vec![7, 10, 4, 3, 20, 15, 1, 8, 12];
        assert_eq!(*median_of_medians_select(&mut arr, 0).unwrap(), 1);
        assert_eq!(*median_of_medians_select(&mut arr, 4).unwrap(), 8);
        assert_eq!(*median_of_medians_select(&mut arr, 8).unwrap(), 20);
    }

    #[test]
    fn test_find_median() {
        let mut arr = vec![7, 10, 4, 3, 20];
        assert_eq!(*find_median(&mut arr).unwrap(), 7);

        let mut arr2 = vec![7, 10, 4, 3, 20, 15];
        assert_eq!(*find_median(&mut arr2).unwrap(), 10);
    }

    #[test]
    fn test_find_min_max() {
        let mut arr = vec![7, 10, 4, 3, 20];
        assert_eq!(*find_min(&mut arr).unwrap(), 3);
        assert_eq!(*find_max(&mut arr).unwrap(), 20);
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (0..1000).rev().collect();
        for i in 0..1000 {
            assert_eq!(*quick_select(&mut arr, i).unwrap(), i as i32);
        }
    }

    #[test]
    fn test_mom_large_array() {
        let mut arr: Vec<i32> = (0..100).rev().collect();
        for i in 0..100 {
            assert_eq!(*median_of_medians_select(&mut arr, i).unwrap(), i as i32);
        }
    }
}
