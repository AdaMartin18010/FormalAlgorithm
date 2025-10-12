//! # 搜索算法 / Searching Algorithms
//!
//! 实现经典搜索算法及其形式化规范。

/// 二分搜索 / Binary Search
///
/// # 形式化定义 / Formal Definition
///
/// 二分搜索在已排序数组中查找目标值：
/// 1. **比较中间元素**: 如果等于目标值，返回索引
/// 2. **缩小范围**: 如果目标值小于中间元素，搜索左半部分；否则搜索右半部分
/// 3. **递归或迭代**: 重复上述过程直到找到目标或范围为空
///
/// ## 前提条件 / Precondition
/// - 数组必须已排序（升序）
///
/// ## 后置条件 / Postcondition
/// - 如果找到，返回 Some(index)，其中 arr[index] == target
/// - 如果未找到，返回 None
///
/// ## 时间复杂度 / Time Complexity
/// - 最好情况: O(1) - 目标在中间
/// - 平均情况: O(log n)
/// - 最坏情况: O(log n)
///
/// ## 空间复杂度 / Space Complexity
/// - O(1) - 迭代实现
/// - O(log n) - 递归实现（调用栈）
///
/// ## 循环不变量 / Loop Invariant
/// - 如果目标存在于数组中，则必定在 [left, right] 范围内
///
/// # 参考文献 / References
/// - [CLRS2009] Cormen et al., "Introduction to Algorithms", 第3版, 第2.3节
/// - 对应文档: `docs/09-算法理论/01-算法基础/02-算法分析.md`
///
/// # Examples
///
/// ```
/// use algorithms::searching::binary_search;
///
/// let arr = vec![1, 3, 5, 7, 9, 11, 13];
/// assert_eq!(binary_search(&arr, 7), Some(3));
/// assert_eq!(binary_search(&arr, 4), None);
/// ```
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mut left = 0;
    let mut right = arr.len() - 1;
    
    // 循环不变量: 如果 target 存在，则在 arr[left..=right] 中
    while left <= right {
        let mid = left + (right - left) / 2;
        
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => {
                // target 在右半部分
                if mid == arr.len() - 1 {
                    break;
                }
                left = mid + 1;
            }
            std::cmp::Ordering::Greater => {
                // target 在左半部分
                if mid == 0 {
                    break;
                }
                right = mid - 1;
            }
        }
    }
    
    None
}

/// 二分搜索（递归实现）/ Binary Search (Recursive)
///
/// 递归版本的二分搜索，便于理解算法的递归性质。
///
/// # Examples
///
/// ```
/// use algorithms::searching::binary_search_recursive;
///
/// let arr = vec![1, 3, 5, 7, 9, 11, 13];
/// assert_eq!(binary_search_recursive(&arr, 7), Some(3));
/// ```
pub fn binary_search_recursive<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    binary_search_helper(arr, target, 0, arr.len())
}

fn binary_search_helper<T: Ord>(
    arr: &[T],
    target: &T,
    offset: usize,
    len: usize,
) -> Option<usize> {
    if len == 0 {
        return None;
    }
    
    let mid = len / 2;
    let mid_index = offset + mid;
    
    match arr[mid_index].cmp(target) {
        std::cmp::Ordering::Equal => Some(mid_index),
        std::cmp::Ordering::Less => {
            // 搜索右半部分
            binary_search_helper(arr, target, mid_index + 1, len - mid - 1)
        }
        std::cmp::Ordering::Greater => {
            // 搜索左半部分
            binary_search_helper(arr, target, offset, mid)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_binary_search_found() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search(&arr, &7), Some(3));
        assert_eq!(binary_search(&arr, &1), Some(0));
        assert_eq!(binary_search(&arr, &13), Some(6));
    }
    
    #[test]
    fn test_binary_search_not_found() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search(&arr, &0), None);
        assert_eq!(binary_search(&arr, &14), None);
        assert_eq!(binary_search(&arr, &6), None);
    }
    
    #[test]
    fn test_binary_search_empty() {
        let arr: Vec<i32> = vec![];
        assert_eq!(binary_search(&arr, &5), None);
    }
    
    #[test]
    fn test_binary_search_single() {
        let arr = vec![42];
        assert_eq!(binary_search(&arr, &42), Some(0));
        assert_eq!(binary_search(&arr, &41), None);
    }
    
    #[test]
    fn test_binary_search_recursive() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search_recursive(&arr, &7), Some(3));
        assert_eq!(binary_search_recursive(&arr, &4), None);
    }
}

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn test_binary_search_finds_existing(mut vec in prop::collection::vec(any::<i32>(), 1..100)) {
            vec.sort();
            let target_idx = vec.len() / 2;
            let target = vec[target_idx];
            
            let result = binary_search(&vec, &target);
            assert!(result.is_some());
            let found_idx = result.unwrap();
            assert_eq!(vec[found_idx], target);
        }
        
        #[test]
        fn test_binary_search_consistent_with_linear(mut vec in prop::collection::vec(any::<i32>(), 0..100), target in any::<i32>()) {
            vec.sort();
            let binary_result = binary_search(&vec, &target);
            let linear_result = vec.iter().position(|x| x == &target);
            
            match (binary_result, linear_result) {
                (Some(_), Some(_)) => { /* 都找到了，正确 */ },
                (None, None) => { /* 都没找到，正确 */ },
                _ => panic!("二分搜索和线性搜索结果不一致"),
            }
        }
    }
}

