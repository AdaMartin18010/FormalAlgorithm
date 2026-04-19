//! 插入排序实现
//!
//! 插入排序是一种简单直观的比较排序算法，工作方式类似于整理手中的扑克牌。
//! 对于小规模数据或基本有序的数据，插入排序是非常高效的选择。
//!
//! 对标: CLRS 4th Ed. Ch 2.1（Getting Started 的核心教学算法）。
//! 亦为 MIT 6.006、Stanford CS161、CMU 15-451 等课程的入门首选算法。
//!
//! ## 算法说明
//!
//! 1. 将数组分为已排序区和未排序区（初始时已排序区只有第一个元素）
//! 2. 从未排序区取出第一个元素，在已排序区中从后向前扫描
//! 3. 找到合适位置并插入，使已排序区保持有序
//! 4. 重复步骤 2-3 直到未排序区为空
//!
//! ## 正确性证明（循环不变式）
//!
//! **循环不变式**：在第 i 次迭代开始时，子数组 `arr[0..i]` 已按非递减顺序排列。
//!
//! - **初始化**：i = 1 时，`arr[0..1]` 只含一个元素，自然有序。
//! - **保持**：假设 `arr[0..i]` 有序，将 `arr[i]` 向前插入到正确位置后，`arr[0..i+1]` 仍有序。
//! - **终止**：i = n 时，`arr[0..n]` 即整个数组有序。
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：
//!   - 最坏情况：O(n²) —— 数组逆序
//!   - 最好情况：O(n) —— 数组已有序
//!   - 平均情况：O(n²)
//! - **空间复杂度**：O(1) —— 原地排序
//! - **稳定性**：稳定排序 —— 相等元素的相对顺序不变
//!
//! ## 实际应用
//!
//! - 小规模数据（n < 50）的首选排序
//! - 作为 Timsort / Introsort 的底层子程序（处理小片段）
//! - 在线排序：数据流逐个到达时的实时排序

/// 对可变切片进行插入排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::insertion_sort::insertion_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// insertion_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn insertion_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 1..n {
        // 将 arr[i] 插入到已排序子数组 arr[0..i] 的正确位置
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// 插入排序的泛型版本，使用自定义比较器
///
/// # 示例
///
/// ```
/// use formal_algorithms::insertion_sort::insertion_sort_by;
///
/// let mut data = vec![(3, "c"), (1, "a"), (2, "b")];
/// insertion_sort_by(&mut data, |a, b| a.0.cmp(&b.0));
/// assert_eq!(data, vec![(1, "a"), (2, "b"), (3, "c")]);
/// ```
pub fn insertion_sort_by<T>(arr: &mut [T], mut compare: impl FnMut(&T, &T) -> std::cmp::Ordering) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 1..n {
        let mut j = i;
        while j > 0 && compare(&arr[j - 1], &arr[j]) == std::cmp::Ordering::Greater {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// 插入排序的优化版本：使用二分查找确定插入位置
///
/// 将线性搜索改为二分查找，减少比较次数，但移动次数不变。
/// 比较复杂度：O(n log n)；移动复杂度：O(n²)。
///
/// # 示例
///
/// ```
/// use formal_algorithms::insertion_sort::insertion_sort_binary;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// insertion_sort_binary(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn insertion_sort_binary<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 1..n {
        // 二分查找插入位置
        let key = i; // 当前要插入的元素位置
        let mut left = 0;
        let mut right = i;

        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] <= arr[key] {
                left = mid + 1;
            } else {
                right = mid;
            }
        }

        // 将 arr[left..i] 后移一位，然后将 arr[i] 插入到 left 位置
        // 注意：由于需要保持所有权，使用循环逐个交换
        let mut j = i;
        while j > left {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// 对近乎有序的数组进行插入排序（最好情况优化）
///
/// 若数组已有序或接近有序，插入排序的时间接近 O(n)。
///
/// # 示例
///
/// ```
/// use formal_algorithms::insertion_sort::insertion_sort;
///
/// let mut data = vec![1, 2, 3, 4, 5, 6, 7];
/// insertion_sort(&mut data);
/// assert_eq!(data, vec![1, 2, 3, 4, 5, 6, 7]);
/// ```

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = vec![];
        insertion_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        insertion_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        insertion_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        insertion_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        insertion_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        insertion_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_stability() {
        let mut arr = vec![(3, 0), (1, 1), (2, 2), (1, 3)];
        insertion_sort_by(&mut arr, |a, b| a.0.cmp(&b.0));
        // 相等键 1 应保持原始相对顺序：(1, 1) 在 (1, 3) 之前
        assert_eq!(arr[0], (1, 1));
        assert_eq!(arr[1], (1, 3));
    }

    #[test]
    fn test_binary_version() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        insertion_sort_binary(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_large_random() {
        let mut arr: Vec<i32> = (0..1000).map(|i| (1000 - i) % 137).collect();
        insertion_sort(&mut arr);
        for i in 1..arr.len() {
            assert!(arr[i - 1] <= arr[i]);
        }
    }
}
