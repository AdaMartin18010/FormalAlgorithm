//! 选择排序实现
//!
//! 选择排序是一种简单直观的比较排序算法，其核心思想是反复从未排序部分选择最小（或最大）元素，
//! 放到已排序部分的末尾。
//!
//! 对标: CLRS 4th Ed. 习题 2.2-2；MIT 6.006、Stanford CS161 等课程的入门教学内容。
//!
//! ## 算法说明
//!
//! 1. 将数组分为已排序区（初始为空）和未排序区
//! 2. 在未排序区中找到最小元素的索引
//! 3. 将该最小元素与未排序区的第一个元素交换
//! 4. 已排序区扩展一位，重复步骤 2-3
//!
//! ## 正确性证明（循环不变式）
//!
//! **循环不变式**：在第 i 次迭代开始时，子数组 `arr[0..i]` 包含原数组中 i 个最小元素，且已按非递减顺序排列。
//!
//! - **初始化**：i = 0 时，`arr[0..0]` 为空，满足不变式。
//! - **保持**：假设 `arr[0..i]` 已包含 i 个最小元素。第 i 次迭代在未排序区 `arr[i..n]` 中找到最小元素并放到位置 i，因此 `arr[0..i+1]` 包含 i+1 个最小元素且有序。
//! - **终止**：i = n-1 时，`arr[0..n-1]` 包含 n-1 个最小元素，则 `arr[n-1]` 必为最大元素，整个数组有序。
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：
//!   - 最坏情况：O(n²) —— 必须进行约 n²/2 次比较
//!   - 最好情况：O(n²) —— 即使数组已有序，仍需完整比较
//!   - 平均情况：O(n²)
//! - **空间复杂度**：O(1) —— 原地排序，最多交换 n-1 次
//! - **稳定性**：不稳定排序 —— 交换可能改变相等元素的相对顺序
//!
//! ## 与插入排序的对比
//!
//! | 特性 | 选择排序 | 插入排序 |
//! |------|---------|---------|
//! | 最好情况 | O(n²) | O(n) |
//! | 比较次数 | ~n²/2（固定） | 取决于输入有序度 |
//! | 交换次数 | O(n)（最多 n-1 次） | O(n²) |
//! | 稳定性 | 不稳定 | 稳定 |
//! | 适用场景 | 交换代价高时 | 基本有序数据 |

/// 对可变切片进行选择排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::selection_sort::selection_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// selection_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn selection_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 0..n - 1 {
        // 在未排序区 arr[i..n] 中找到最小元素的索引
        let mut min_idx = i;
        for j in i + 1..n {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        // 将最小元素交换到位置 i
        if min_idx != i {
            arr.swap(i, min_idx);
        }
    }
}

/// 选择排序的泛型版本，使用自定义比较器
///
/// # 示例
///
/// ```
/// use formal_algorithms::selection_sort::selection_sort_by;
///
/// let mut data = vec![(3, "c"), (1, "a"), (2, "b")];
/// selection_sort_by(&mut data, |a, b| a.0.cmp(&b.0));
/// assert_eq!(data, vec![(1, "a"), (2, "b"), (3, "c")]);
/// ```
pub fn selection_sort_by<T>(arr: &mut [T], mut compare: impl FnMut(&T, &T) -> std::cmp::Ordering) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 0..n - 1 {
        let mut min_idx = i;
        for j in i + 1..n {
            if compare(&arr[j], &arr[min_idx]) == std::cmp::Ordering::Less {
                min_idx = j;
            }
        }
        if min_idx != i {
            arr.swap(i, min_idx);
        }
    }
}

/// 双向选择排序（每次同时找最小和最大）
///
/// 将比较次数从 ~n²/2 减少到 ~n²/2（比较次数相同），
/// 但交换次数减少到 ~n/2。
///
/// # 示例
///
/// ```
/// use formal_algorithms::selection_sort::bidirectional_selection_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// bidirectional_selection_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn bidirectional_selection_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    let mut left = 0;
    let mut right = n - 1;

    while left < right {
        let mut min_idx = left;
        let mut max_idx = left;

        for i in left..=right {
            if arr[i] < arr[min_idx] {
                min_idx = i;
            }
            if arr[i] > arr[max_idx] {
                max_idx = i;
            }
        }

        // 将最小元素放到 left
        arr.swap(left, min_idx);

        // 如果 max_idx 是 left，它已经被换到了 min_idx 的位置
        if max_idx == left {
            max_idx = min_idx;
        }

        // 将最大元素放到 right
        arr.swap(right, max_idx);

        left += 1;
        right -= 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = vec![];
        selection_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        selection_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        selection_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        selection_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        selection_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        selection_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_bidirectional() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        bidirectional_selection_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_large_random() {
        let mut arr: Vec<i32> = (0..1000).map(|i| (1000 - i) % 137).collect();
        selection_sort(&mut arr);
        for i in 1..arr.len() {
            assert!(arr[i - 1] <= arr[i]);
        }
    }
}
