//! 冒泡排序实现
//!
//! 冒泡排序是一种简单直观的比较排序算法，通过反复遍历数组，
//! 比较相邻元素并在顺序错误时交换它们，使较大（或较小）的元素逐渐"冒泡"到数组末尾。
//!
//! 对标: CLRS 4th Ed. 习题 2-2；MIT 6.006、Stanford CS161 等课程的入门教学内容。
//! 虽然实际应用中很少使用，但冒泡排序是教学中最直观的排序算法之一。
//!
//! ## 算法说明
//!
//! 1. 从数组起始位置开始，比较相邻的两个元素
//! 2. 如果顺序错误（前一个大于后一个），则交换它们
//! 3. 移动到下一对相邻元素，重复步骤 2
//! 4. 一轮遍历后，最大元素会"冒泡"到数组末尾
//! 5. 对未排序部分重复上述过程
//!
//! ## 正确性证明（循环不变式）
//!
//! **循环不变式**：在第 i 轮外层循环结束时，子数组 `arr[n-i..n]` 包含原数组中 i 个最大元素，且已按非递减顺序排列。
//!
//! - **初始化**：i = 0 时，`arr[n..n]` 为空，满足不变式。
//! - **保持**：每一轮内层循环将未排序区中的最大元素推到该区末尾，因此第 i 轮后 `arr[n-i-1]` 为剩余未排序区的最大元素。
//! - **终止**：i = n-1 时，`arr[1..n]` 包含 n-1 个最大元素且有序，则 `arr[0]` 必为最小元素，整个数组有序。
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：
//!   - 最坏情况：O(n²) —— 数组逆序
//!   - 最好情况：O(n) —— 数组已有序（优化版本）
//!   - 平均情况：O(n²)
//! - **空间复杂度**：O(1) —— 原地排序
//! - **稳定性**：稳定排序 —— 相等元素不会交换，相对顺序保持不变
//!
//! ## 优化变体
//!
//! - **提前终止**：若一轮遍历中没有发生任何交换，则数组已有序，可直接终止
//! - **鸡尾酒排序（Cocktail Shaker Sort）**：双向冒泡，同时让最小和最大元素归位
//! - **梳排序（Comb Sort）**：用递减的间隔比较替代相邻比较，消除"乌龟"（小数在末尾）问题

/// 对可变切片进行冒泡排序（基础版本）
///
/// # 示例
///
/// ```
/// use formal_algorithms::bubble_sort::bubble_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// bubble_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn bubble_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 0..n {
        for j in 0..n - 1 - i {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

/// 优化冒泡排序（提前终止版本）
///
/// 若某一轮没有发生交换，说明数组已有序，直接终止。
/// 最好情况时间复杂度：O(n)。
///
/// # 示例
///
/// ```
/// use formal_algorithms::bubble_sort::bubble_sort_optimized;
///
/// let mut data = vec![1, 2, 3, 4, 5];
/// bubble_sort_optimized(&mut data);
/// assert_eq!(data, vec![1, 2, 3, 4, 5]);
/// ```
pub fn bubble_sort_optimized<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    for i in 0..n {
        let mut swapped = false;
        for j in 0..n - 1 - i {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
    }
}

/// 鸡尾酒排序（双向冒泡排序）
///
/// 每一轮同时从两端向中间"冒泡"：
/// - 从左到右将最大元素推到右侧
/// - 从右到左将最小元素推到左侧
///
/// 可减少"乌龟"（位于末尾的小元素）导致的低效遍历。
///
/// # 示例
///
/// ```
/// use formal_algorithms::bubble_sort::cocktail_shaker_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// cocktail_shaker_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn cocktail_shaker_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    let mut left = 0;
    let mut right = n - 1;

    while left < right {
        let mut new_right = left;
        for i in left..right {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                new_right = i;
            }
        }
        right = new_right;

        if left >= right {
            break;
        }

        let mut new_left = right;
        for i in (left..right).rev() {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                new_left = i + 1;
            }
        }
        left = new_left;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = vec![];
        bubble_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        bubble_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        bubble_sort_optimized(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        bubble_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        bubble_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        bubble_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_cocktail_shaker() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        cocktail_shaker_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_optimized_early_termination() {
        let mut arr = vec![1, 2, 3, 4, 5];
        bubble_sort_optimized(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_stability() {
        let mut arr = vec![(3, 0), (1, 1), (2, 2), (1, 3)];
        bubble_sort(&mut arr);
        // 冒泡排序是稳定的
        assert_eq!(arr[0], (1, 1));
        assert_eq!(arr[1], (1, 3));
    }

    #[test]
    fn test_large_random() {
        let mut arr: Vec<i32> = (0..500).map(|i| (500 - i) % 137).collect();
        bubble_sort_optimized(&mut arr);
        for i in 1..arr.len() {
            assert!(arr[i - 1] <= arr[i]);
        }
    }
}
