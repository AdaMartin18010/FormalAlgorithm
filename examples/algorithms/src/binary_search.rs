//! 二分搜索实现
//!
//! 二分搜索是一种在有序数组中查找元素的高效算法。

use crate::{AlgorithmError, SearchResult};

/// 在有序数组中进行二分搜索
///
/// # 算法说明
///
/// 二分搜索通过反复将搜索区间减半来工作：
/// 1. 比较目标值与数组中间元素
/// 2. 如果相等，返回索引
/// 3. 如果目标值较小，在左半部分继续搜索
/// 4. 如果目标值较大，在右半部分继续搜索
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n)
///   - 每次迭代将搜索范围减半
/// - **空间复杂度**：O(1) - 迭代实现
/// - **空间复杂度**：O(log n) - 递归实现
///
/// # 参数
///
/// * `arr` - 已排序的数组（升序）
/// * `target` - 要查找的目标值
///
/// # 返回值
///
/// * `Ok(index)` - 找到目标值，返回其索引
/// * `Err(AlgorithmError::NotFound)` - 未找到目标值
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search;
///
/// let arr = vec![1, 3, 5, 7, 9, 11, 13];
/// assert_eq!(binary_search(&arr, 7), Ok(3));
/// assert_eq!(binary_search(&arr, 6), Err(formal_algorithms::AlgorithmError::NotFound));
/// ```
///
/// # 注意事项
///
/// * 数组必须已排序（升序），否则结果不可预期
/// * 如果数组中有多个相等的元素，返回任意一个的索引
pub fn binary_search<T: Ord>(arr: &[T], target: T) -> SearchResult<usize> {
    if arr.is_empty() {
        return Err(AlgorithmError::NotFound);
    }

    let mut low = 0;
    let mut high = arr.len() - 1;

    while low <= high {
        let mid = low + (high - low) / 2;

        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Ok(mid),
            std::cmp::Ordering::Less => {
                // 防止整数溢出
                if mid == arr.len() - 1 {
                    break;
                }
                low = mid + 1;
            }
            std::cmp::Ordering::Greater => {
                if mid == 0 {
                    break;
                }
                high = mid - 1;
            }
        }
    }

    Err(AlgorithmError::NotFound)
}

/// 二分搜索的递归实现
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::binary_search_recursive;
///
/// let arr = vec![1, 3, 5, 7, 9];
/// assert_eq!(binary_search_recursive(&arr, 7, 0, arr.len()), Ok(3));
/// ```
pub fn binary_search_recursive<T: Ord>(
    arr: &[T],
    target: T,
    low: usize,
    high: usize,
) -> SearchResult<usize> {
    if low >= high {
        return Err(AlgorithmError::NotFound);
    }

    let mid = low + (high - low) / 2;

    match arr[mid].cmp(&target) {
        std::cmp::Ordering::Equal => Ok(mid),
        std::cmp::Ordering::Less => binary_search_recursive(arr, target, mid + 1, high),
        std::cmp::Ordering::Greater => {
            if mid == 0 {
                Err(AlgorithmError::NotFound)
            } else {
                binary_search_recursive(arr, target, low, mid)
            }
        }
    }
}

/// 查找第一个大于等于目标值的索引（lower_bound）
///
/// 如果数组中有多个相等的元素，返回第一个的索引。
/// 如果所有元素都小于目标值，返回数组长度。
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::lower_bound;
///
/// let arr = vec![1, 2, 2, 2, 3, 4, 5];
/// assert_eq!(lower_bound(&arr, 2), 1);  // 第一个2的位置
/// assert_eq!(lower_bound(&arr, 0), 0);  // 所有元素都大于0
/// assert_eq!(lower_bound(&arr, 6), 7);  // 所有元素都小于6
/// ```
pub fn lower_bound<T: Ord>(arr: &[T], target: T) -> usize {
    let mut low = 0;
    let mut high = arr.len();

    while low < high {
        let mid = low + (high - low) / 2;
        if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }

    low
}

/// 查找第一个大于目标值的索引（upper_bound）
///
/// 如果数组中有多个相等的元素，返回最后一个的下一个索引。
/// 如果所有元素都小于等于目标值，返回数组长度。
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::upper_bound;
///
/// let arr = vec![1, 2, 2, 2, 3, 4, 5];
/// assert_eq!(upper_bound(&arr, 2), 4);  // 最后一个2的下一个位置
/// assert_eq!(upper_bound(&arr, 0), 0);  // 所有元素都大于0
/// assert_eq!(upper_bound(&arr, 5), 7);  // 所有元素都小于等于5
/// ```
pub fn upper_bound<T: Ord>(arr: &[T], target: T) -> usize {
    let mut low = 0;
    let mut high = arr.len();

    while low < high {
        let mid = low + (high - low) / 2;
        if arr[mid] <= target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }

    low
}

/// 查找目标值的范围
///
/// 返回 (lower_bound, upper_bound)，即目标值在数组中的起始和结束位置（左闭右开）。
/// 如果目标值不存在，返回 (插入位置, 插入位置)。
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::equal_range;
///
/// let arr = vec![1, 2, 2, 2, 3, 4, 5];
/// assert_eq!(equal_range(&arr, 2), (1, 4));  // 2出现在索引1,2,3
/// assert_eq!(equal_range(&arr, 6), (7, 7));  // 6不存在，应插入到位置7
/// ```
pub fn equal_range<T: Ord>(arr: &[T], target: T) -> (usize, usize) {
    (lower_bound(arr, target), upper_bound(arr, target))
}

/// 查找目标值出现的次数
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::count;
///
/// let arr = vec![1, 2, 2, 2, 3, 4, 5];
/// assert_eq!(count(&arr, 2), 3);
/// assert_eq!(count(&arr, 6), 0);
/// ```
pub fn count<T: Ord>(arr: &[T], target: T) -> usize {
    let (start, end) = equal_range(arr, target);
    end - start
}

/// 查找目标值在有序数组中的插入位置（保持有序）
///
/// 返回应插入的位置，使得插入后数组仍保持有序。
/// 如果目标值已存在，返回其位置（可用于实现stable插入）。
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::insertion_point;
///
/// let arr = vec![1, 3, 5, 7, 9];
/// assert_eq!(insertion_point(&arr, 6), 3);  // 应插入到索引3
/// ```
pub fn insertion_point<T: Ord>(arr: &[T], target: T) -> usize {
    lower_bound(arr, target)
}

/// 二分搜索查找旋转排序数组中的最小值
///
/// 数组被旋转了k次（例如 [3,4,5,1,2] 是 [1,2,3,4,5] 旋转3次的结果）
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::find_min_in_rotated;
///
/// let arr = vec![3, 4, 5, 1, 2];
/// assert_eq!(find_min_in_rotated(&arr), Ok(&1));
/// ```
pub fn find_min_in_rotated<T: Ord>(arr: &[T]) -> SearchResult<&T> {
    if arr.is_empty() {
        return Err(AlgorithmError::InvalidInput("Empty array".to_string()));
    }

    let mut low = 0;
    let mut high = arr.len() - 1;

    while low < high {
        let mid = low + (high - low) / 2;

        if arr[mid] > arr[high] {
            // 最小值在右半部分
            low = mid + 1;
        } else {
            // arr[mid] <= arr[high]，最小值在左半部分或就是mid
            high = mid;
        }
    }

    Ok(&arr[low])
}

/// 在旋转排序数组中搜索目标值
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::search_in_rotated;
///
/// let arr = vec![4, 5, 6, 7, 0, 1, 2];
/// assert_eq!(search_in_rotated(&arr, 0), Ok(4));
/// assert_eq!(search_in_rotated(&arr, 3), Err(formal_algorithms::AlgorithmError::NotFound));
/// ```
pub fn search_in_rotated<T: Ord>(arr: &[T], target: T) -> SearchResult<usize> {
    if arr.is_empty() {
        return Err(AlgorithmError::NotFound);
    }

    let mut low = 0;
    let mut high = arr.len() - 1;

    while low <= high {
        let mid = low + (high - low) / 2;

        if arr[mid] == target {
            return Ok(mid);
        }

        // 判断哪一半是有序的
        if arr[low] <= arr[mid] {
            // 左半部分有序
            if arr[low] <= target && target < arr[mid] {
                if mid == 0 {
                    break;
                }
                high = mid - 1;
            } else {
                low = mid + 1;
            }
        } else {
            // 右半部分有序
            if arr[mid] < target && target <= arr[high] {
                low = mid + 1;
            } else {
                if mid == 0 {
                    break;
                }
                high = mid - 1;
            }
        }
    }

    Err(AlgorithmError::NotFound)
}

/// 二分查找平方根（整数）
///
/// 返回 x 的平方根向下取整的结果
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_search::sqrt_int;
///
/// assert_eq!(sqrt_int(8), 2);
/// assert_eq!(sqrt_int(9), 3);
/// assert_eq!(sqrt_int(10), 3);
/// ```
pub fn sqrt_int(x: u64) -> u64 {
    if x < 2 {
        return x;
    }

    let mut low = 1;
    let mut high = x / 2;
    let mut ans = 0;

    while low <= high {
        let mid = low + (high - low) / 2;
        let square = mid * mid;

        if square == x {
            return mid;
        } else if square < x {
            ans = mid;
            low = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }

    ans
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_array() {
        let arr: Vec<i32> = vec![];
        assert_eq!(binary_search(&arr, 5), Err(AlgorithmError::NotFound));
    }

    #[test]
    fn test_single_element() {
        let arr = vec![42];
        assert_eq!(binary_search(&arr, 42), Ok(0));
        assert_eq!(binary_search(&arr, 10), Err(AlgorithmError::NotFound));
    }

    #[test]
    fn test_basic_search() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search(&arr, 7), Ok(3));
        assert_eq!(binary_search(&arr, 1), Ok(0));
        assert_eq!(binary_search(&arr, 13), Ok(6));
    }

    #[test]
    fn test_not_found() {
        let arr = vec![1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, 0), Err(AlgorithmError::NotFound));
        assert_eq!(binary_search(&arr, 6), Err(AlgorithmError::NotFound));
        assert_eq!(binary_search(&arr, 10), Err(AlgorithmError::NotFound));
    }

    #[test]
    fn test_duplicate_elements() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        let result = binary_search(&arr, 2);
        assert!(result.is_ok());
        let idx = result.unwrap();
        assert!(idx >= 1 && idx <= 3);
    }

    #[test]
    fn test_large_array() {
        let arr: Vec<i32> = (0..10000).collect();
        assert_eq!(binary_search(&arr, 5000), Ok(5000));
        assert_eq!(binary_search(&arr, 9999), Ok(9999));
    }

    #[test]
    fn test_lower_bound() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        assert_eq!(lower_bound(&arr, 2), 1);
        assert_eq!(lower_bound(&arr, 0), 0);
        assert_eq!(lower_bound(&arr, 6), 7);
    }

    #[test]
    fn test_upper_bound() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        assert_eq!(upper_bound(&arr, 2), 4);
        assert_eq!(upper_bound(&arr, 0), 0);
        assert_eq!(upper_bound(&arr, 5), 7);
    }

    #[test]
    fn test_equal_range() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        assert_eq!(equal_range(&arr, 2), (1, 4));
        assert_eq!(equal_range(&arr, 6), (7, 7));
    }

    #[test]
    fn test_count() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        assert_eq!(count(&arr, 2), 3);
        assert_eq!(count(&arr, 6), 0);
    }

    #[test]
    fn test_recursive_search() {
        let arr = vec![1, 3, 5, 7, 9];
        assert_eq!(binary_search_recursive(&arr, 7, 0, arr.len()), Ok(3));
        assert_eq!(binary_search_recursive(&arr, 6, 0, arr.len()), Err(AlgorithmError::NotFound));
    }

    #[test]
    fn test_find_min_in_rotated() {
        let arr = vec![3, 4, 5, 1, 2];
        assert_eq!(find_min_in_rotated(&arr), Ok(&1));

        let arr2 = vec![1, 2, 3, 4, 5];
        assert_eq!(find_min_in_rotated(&arr2), Ok(&1));
    }

    #[test]
    fn test_search_in_rotated() {
        let arr = vec![4, 5, 6, 7, 0, 1, 2];
        assert_eq!(search_in_rotated(&arr, 0), Ok(4));
        assert_eq!(search_in_rotated(&arr, 3), Err(AlgorithmError::NotFound));
    }

    #[test]
    fn test_sqrt_int() {
        assert_eq!(sqrt_int(0), 0);
        assert_eq!(sqrt_int(1), 1);
        assert_eq!(sqrt_int(8), 2);
        assert_eq!(sqrt_int(9), 3);
        assert_eq!(sqrt_int(10), 3);
        assert_eq!(sqrt_int(15), 3);
        assert_eq!(sqrt_int(16), 4);
    }

    #[test]
    fn test_string_search() {
        let arr = vec!["apple", "banana", "cherry", "date"];
        assert_eq!(binary_search(&arr, "cherry"), Ok(2));
        assert_eq!(binary_search(&arr, "grape"), Err(AlgorithmError::NotFound));
    }
}
