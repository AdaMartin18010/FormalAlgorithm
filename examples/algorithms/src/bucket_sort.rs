//! 桶排序实现
//!
//! 桶排序假设输入数据近似均匀分布于 [0, 1) 区间。
//! 通过将数据分桶后对各桶单独排序，期望时间复杂度为 O(n)。

/// 桶排序（浮点数版本）
///
/// 对 [0.0, 1.0) 范围内的 f64 数组进行桶排序。
/// 将 [0, 1) 划分为 n 个等宽桶，每个桶内使用插入排序。
///
/// # 算法说明
///
/// 1. 创建 n 个空桶
/// 2. 将每个元素放入对应的桶中（索引 = floor(n * value)）
/// 3. 对每个非空桶使用插入排序
/// 4. 按顺序拼接所有桶中的元素
///
/// # 复杂度分析
///
/// - **期望时间复杂度**: O(n)（在均匀分布假设下）
/// - **最坏时间复杂度**: O(n²)（所有元素落入同一桶）
/// - **空间复杂度**: O(n)
/// - **稳定性**: 稳定排序（若桶内排序稳定）
///
/// # 示例
///
/// ```
/// use formal_algorithms::bucket_sort;
///
/// let mut data = vec![0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51];
/// bucket_sort(&mut data);
/// assert!(data.windows(2).all(|w| w[0] <= w[1]));
/// ```
pub fn bucket_sort(arr: &mut [f64]) {
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();
    let mut buckets: Vec<Vec<f64>> = vec![Vec::new(); n];

    // 将元素分配到桶中
    for &val in arr.iter() {
        let bucket_index = ((val.clamp(0.0, 0.999999999) * n as f64) as usize).min(n - 1);
        buckets[bucket_index].push(val);
    }

    // 对每个桶进行插入排序
    for bucket in buckets.iter_mut() {
        bucket.sort_by(|a, b| a.partial_cmp(b).unwrap());
    }

    // 按顺序拼接回原始数组
    let mut idx = 0;
    for bucket in buckets {
        for val in bucket {
            arr[idx] = val;
            idx += 1;
        }
    }
}

/// 泛型桶排序
///
/// 通过提供值到 [0, 1) 的映射函数，可以对任意类型进行桶排序。
///
/// # 类型参数
///
/// * `T` - 元素类型，需要实现 Clone
/// * `F` - 映射函数类型，将元素映射到 [0.0, 1.0)
///
/// # 示例
///
/// ```
/// use formal_algorithms::bucket_sort::bucket_sort_by;
///
/// let mut data = vec![(42, 42), (32, 32), (33, 33)];
/// bucket_sort_by(&mut data, |x| x.1 as f64 / 100.0);
/// assert_eq!(data, vec![(32, 32), (33, 33), (42, 42)]);
/// ```
pub fn bucket_sort_by<T: Clone + Ord>(arr: &mut [T], to_unit: impl Fn(&T) -> f64) {
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();
    let mut buckets: Vec<Vec<T>> = vec![Vec::new(); n];

    for item in arr.iter() {
        let key = to_unit(item);
        let bucket_index = ((key.clamp(0.0, 0.999999999) * n as f64) as usize).min(n - 1);
        buckets[bucket_index].push(item.clone());
    }

    for bucket in buckets.iter_mut() {
        bucket.sort();
    }

    let mut idx = 0;
    for bucket in buckets {
        for item in bucket {
            arr[idx] = item;
            idx += 1;
        }
    }
}

/// 将任意区间 [min, max) 的浮点数映射到 [0, 1) 后进行桶排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::bucket_sort::bucket_sort_range;
///
/// let mut data = vec![42.0, 32.0, 33.0, 52.0, 37.0];
/// bucket_sort_range(&mut data, 30.0, 55.0);
/// assert_eq!(data, vec![32.0, 33.0, 37.0, 42.0, 52.0]);
/// ```
pub fn bucket_sort_range(arr: &mut [f64], min_val: f64, max_val: f64) {
    assert!(max_val > min_val, "max_val must be greater than min_val");

    // 临时归一化
    let range = max_val - min_val;
    for val in arr.iter_mut() {
        *val = ((*val - min_val) / range).clamp(0.0, 0.999999999);
    }

    bucket_sort(arr);

    // 反归一化
    for val in arr.iter_mut() {
        *val = *val * range + min_val;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut arr: Vec<f64> = vec![];
        bucket_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![0.5];
        bucket_sort(&mut arr);
        assert_eq!(arr, vec![0.5]);
    }

    #[test]
    fn test_basic() {
        let mut arr = vec![0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51];
        bucket_sort(&mut arr);
        assert_eq!(arr, vec![0.32, 0.33, 0.37, 0.42, 0.47, 0.51, 0.52]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![0.1, 0.2, 0.3, 0.4, 0.5];
        bucket_sort(&mut arr);
        assert_eq!(arr, vec![0.1, 0.2, 0.3, 0.4, 0.5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![0.9, 0.7, 0.5, 0.3, 0.1];
        bucket_sort(&mut arr);
        assert_eq!(arr, vec![0.1, 0.3, 0.5, 0.7, 0.9]);
    }

    #[test]
    fn test_duplicates() {
        let mut arr = vec![0.5, 0.3, 0.5, 0.1, 0.3];
        bucket_sort(&mut arr);
        assert_eq!(arr, vec![0.1, 0.3, 0.3, 0.5, 0.5]);
    }

    #[test]
    fn test_uniform_random() {
        // 生成近似均匀分布的数据
        let mut arr: Vec<f64> = (0..100).map(|i| i as f64 / 100.0).collect();
        arr.reverse();
        bucket_sort(&mut arr);
        assert!(arr.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_bucket_sort_by() {
        let mut data = vec![(42, 42), (32, 32), (33, 33)];
        bucket_sort_by(&mut data, |x| x.1 as f64 / 100.0);
        assert_eq!(data, vec![(32, 32), (33, 33), (42, 42)]);
    }

    #[test]
    fn test_bucket_sort_range() {
        let mut data = vec![42.0, 32.0, 33.0, 52.0, 37.0];
        bucket_sort_range(&mut data, 30.0, 55.0);
        assert_eq!(data, vec![32.0, 33.0, 37.0, 42.0, 52.0]);
    }
}
