//! 基数排序实现
//!
//! 基数排序是一种非比较排序算法，通过逐位稳定排序实现整体有序。
//! 适用于整数排序，特别是固定位数的整数。

/// LSD (最低位优先) 基数排序
///
/// 对非负整数数组进行原地基数排序，按十进制位逐位排序。
/// 使用稳定的计数排序作为子程序。
///
/// # 算法说明
///
/// 1. 从最低有效位到最高有效位，依次对数组进行稳定计数排序
/// 2. 每位排序后，数组按当前已处理的低位有序
/// 3. 最终按全部位数有序
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(d(n + k))，d 为最大位数，k 为基数（此处 k=10）
/// - **空间复杂度**: O(n + k)
/// - **稳定性**: 稳定排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::radix_sort;
///
/// let mut data = vec![170, 45, 75, 90, 802, 24, 2, 66];
/// radix_sort(&mut data);
/// assert_eq!(data, vec![2, 24, 45, 66, 75, 90, 170, 802]);
/// ```
pub fn radix_sort(arr: &mut [u32]) {
    if arr.len() <= 1 {
        return;
    }

    let max_val = *arr.iter().max().unwrap_or(&0);
    let mut exp = 1u32;

    while max_val / exp > 0 {
        counting_sort_by_digit(arr, exp);
        exp *= 10;
    }
}

/// 按特定位进行稳定计数排序
///
/// 根据元素在 exp 位上的数字（十进制）进行稳定排序。
fn counting_sort_by_digit(arr: &mut [u32], exp: u32) {
    let n = arr.len();
    let mut output = vec![0u32; n];
    let mut count = [0usize; 10];

    // 统计当前位上每个数字的出现次数
    for &val in arr.iter() {
        let digit = ((val / exp) % 10) as usize;
        count[digit] += 1;
    }

    // 计算前缀和，确定每个数字的右边界
    for i in 1..10 {
        count[i] += count[i - 1];
    }

    // 逆序遍历，保持稳定
    for &val in arr.iter().rev() {
        let digit = ((val / exp) % 10) as usize;
        output[count[digit] - 1] = val;
        count[digit] -= 1;
    }

    arr.copy_from_slice(&output);
}

/// 二进制基数排序（按字节排序）
///
/// 将 32 位无符号整数按 8 位一组（共 4 字节）进行基数排序。
/// 这种方法使用 k=256 的计数数组，更适合 CPU 缓存。
///
/// # 示例
///
/// ```
/// use formal_algorithms::radix_sort::radix_sort_u32_by_byte;
///
/// let mut data = vec![0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0x00000000];
/// radix_sort_u32_by_byte(&mut data);
/// assert_eq!(data, vec![0x00000000, 0x12345678, 0xCAFEBABE, 0xDEADBEEF]);
/// ```
pub fn radix_sort_u32_by_byte(arr: &mut [u32]) {
    if arr.len() <= 1 {
        return;
    }

    for shift in (0..4).map(|i| i * 8) {
        counting_sort_by_byte(arr, shift);
    }
}

fn counting_sort_by_byte(arr: &mut [u32], shift: u32) {
    let n = arr.len();
    let mut output = vec![0u32; n];
    let mut count = [0usize; 256];

    for &val in arr.iter() {
        let byte = ((val >> shift) & 0xFF) as usize;
        count[byte] += 1;
    }

    for i in 1..256 {
        count[i] += count[i - 1];
    }

    for &val in arr.iter().rev() {
        let byte = ((val >> shift) & 0xFF) as usize;
        output[count[byte] - 1] = val;
        count[byte] -= 1;
    }

    arr.copy_from_slice(&output);
}

/// 对固定长度字符串进行基数排序（LSD）
///
/// 假设所有字符串长度相同，按字符从低位到高位排序。
///
/// # 示例
///
/// ```
/// use formal_algorithms::radix_sort::radix_sort_strings;
///
/// let mut data = vec![
///     "cat".to_string(),
///     "bat".to_string(),
///     "rat".to_string(),
///     "ant".to_string(),
/// ];
/// radix_sort_strings(&mut data);
/// assert_eq!(data, vec!["ant", "bat", "cat", "rat"]);
/// ```
pub fn radix_sort_strings(arr: &mut [String]) {
    if arr.len() <= 1 {
        return;
    }

    let len = arr[0].len();
    assert!(
        arr.iter().all(|s| s.len() == len),
        "All strings must have the same length"
    );

    for pos in (0..len).rev() {
        counting_sort_by_char(arr, pos);
    }
}

fn counting_sort_by_char(arr: &mut [String], pos: usize) {
    let n = arr.len();
    let mut output = vec![String::new(); n];
    let mut count = [0usize; 256];

    for s in arr.iter() {
        let ch = s.as_bytes()[pos] as usize;
        count[ch] += 1;
    }

    for i in 1..256 {
        count[i] += count[i - 1];
    }

    for s in arr.iter().rev() {
        let ch = s.as_bytes()[pos] as usize;
        output[count[ch] - 1] = s.clone();
        count[ch] -= 1;
    }

    for (i, s) in output.into_iter().enumerate() {
        arr[i] = s;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        radix_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_basic() {
        let mut arr = vec![170, 45, 75, 90, 802, 24, 2, 66];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![2, 24, 45, 66, 75, 90, 170, 802]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![987, 654, 321, 123];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![123, 321, 654, 987]);
    }

    #[test]
    fn test_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_byte_sort() {
        let mut arr = vec![0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0x00000000];
        radix_sort_u32_by_byte(&mut arr);
        assert_eq!(arr, vec![0x00000000, 0x12345678, 0xCAFEBABE, 0xDEADBEEF]);
    }

    #[test]
    fn test_string_sort() {
        let mut arr = vec![
            "cat".to_string(),
            "bat".to_string(),
            "rat".to_string(),
            "ant".to_string(),
        ];
        radix_sort_strings(&mut arr);
        assert_eq!(arr, vec!["ant", "bat", "cat", "rat"]);
    }

    #[test]
    fn test_large_numbers() {
        let mut arr = vec![1_000_000, 999_999, 1, 0, 500_000];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![0, 1, 500_000, 999_999, 1_000_000]);
    }
}
