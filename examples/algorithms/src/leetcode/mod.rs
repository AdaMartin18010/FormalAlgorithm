//! LeetCode 经典题目实现
//!
//! 本模块提供 LeetCode 高频题目的工程级 Rust 实现，
//! 包含完整的形式化规约、循环不变式、复杂度分析与单元测试。
//!
//! 交叉引用：
//! - 算法面试专题：`docs/13-LeetCode算法面试专题/`
//! - 形式化证明：`docs/03-形式化证明/`
//! - 复杂度理论：`docs/04-算法复杂度/`

/// LeetCode 704. 二分查找
pub mod lc0704_binary_search;
/// LeetCode 33. 搜索旋转排序数组
pub mod lc0033_search_in_rotated_sorted_array;
/// LeetCode 153. 寻找旋转排序数组中的最小值
pub mod lc0153_find_minimum_in_rotated_sorted_array;

// 重新导出主要函数以方便使用
pub use lc0704_binary_search::search as lc0704_search;
pub use lc0033_search_in_rotated_sorted_array::search as lc0033_search;
pub use lc0153_find_minimum_in_rotated_sorted_array::find_min as lc0153_find_min;
