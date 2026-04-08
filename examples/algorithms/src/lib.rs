//! # 工程级算法实现库
//!
//! 提供10个核心算法的工程级实现，包含完整的文档、单元测试和性能基准测试。
//!
//! ## 算法清单
//!
//! ### 排序算法 (3个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 归并排序 | [`merge_sort`] | O(n log n) | O(n) |
//! | 快速排序 | [`quick_sort`] | O(n log n) 平均 | O(log n) |
//! | 堆排序 | [`heap_sort`] | O(n log n) | O(1) |
//!
//! ### 搜索算法 (1个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 二分搜索 | [`binary_search`] | O(log n) | O(1) |
//!
//! ### 图算法 (3个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | Dijkstra | [`dijkstra`] | O((V+E) log V) | O(V) |
//! | BFS | [`graph_bfs_dfs::bfs`] | O(V+E) | O(V) |
//! | DFS | [`graph_bfs_dfs::dfs`] | O(V+E) | O(V) |
//!
//! ### 动态规划 (1个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | LCS | [`lcs`] | O(mn) | O(mn) |
//!
//! ### 贪心算法 (1个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 活动选择 | [`greedy_activity_selection`] | O(n log n) | O(n) |
//!
//! ### 回溯算法 (2个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | N皇后 | [`backtracking_nqueens`] | O(N!) | O(N) |
//! | 子集和/图着色 | [`backtracking`] | O(2^n)/O(m^n) | O(n) |
//!
//! ### 分治算法 (1个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 矩阵乘法/最近点对 | [`divide_and_conquer`] | O(n^2.8)/O(n log n) | O(n²)/O(n) |

#![warn(missing_docs)]
#![warn(missing_debug_implementations)]
#![warn(rust_2018_idioms)]

use thiserror::Error;

/// 算法错误类型
#[derive(Error, Debug, Clone, PartialEq)]
pub enum AlgorithmError {
    /// 输入无效
    #[error("Invalid input: {0}")]
    InvalidInput(String),
    /// 元素未找到
    #[error("Element not found")]
    NotFound,
    /// 索引越界
    #[error("Index out of bounds: {index} >= {len}")]
    IndexOutOfBounds {
        /// 越界的索引值
        index: usize,
        /// 集合的长度
        len: usize,
    },
    /// 图相关错误
    #[error("Graph error: {0}")]
    GraphError(String),
    /// 未实现
    #[error("Not implemented: {0}")]
    NotImplemented(String),
}

/// 搜索结果类型
pub type SearchResult<T> = Result<T, AlgorithmError>;

// 排序算法模块
/// 归并排序模块
pub mod merge_sort;
/// 快速排序模块
pub mod quick_sort;
/// 堆排序模块
pub mod heap_sort;

// 搜索算法模块
/// 二分搜索模块
pub mod binary_search;

// 图算法模块
/// Dijkstra算法模块
pub mod dijkstra;
/// 图遍历算法 - BFS/DFS模块
pub mod graph_bfs_dfs;

// 动态规划模块
/// 最长公共子序列模块
pub mod lcs;

// 贪心算法模块
/// 贪心算法 - 活动选择模块
pub mod greedy_activity_selection;

// 回溯算法模块
/// 回溯算法 - N皇后模块
pub mod backtracking_nqueens;
/// 回溯算法 - 通用回溯模块
pub mod backtracking;

// 分治算法模块
/// 分治算法模块
pub mod divide_and_conquer;

// 排序算法
pub use heap_sort::heap_sort;
pub use merge_sort::merge_sort;
pub use quick_sort::quick_sort;

// 搜索算法
pub use binary_search::binary_search;
pub use binary_search::{lower_bound, upper_bound};

// 图算法
pub use dijkstra::dijkstra;
pub use graph_bfs_dfs::{bfs, dfs};

// 动态规划
pub use lcs::lcs;
pub use lcs::lcs_length;

// 贪心算法
pub use greedy_activity_selection::greedy_activity_selection;
pub use greedy_activity_selection::Activity;

// 回溯算法
pub use backtracking_nqueens::solve_n_queens;
pub use backtracking::{subset_sum, graph_coloring, generate_permutations};

// 分治算法
pub use divide_and_conquer::{closest_pair, Point, Matrix, strassen_multiply};

/// 算法 trait，定义算法的基本接口
///
/// 这是用于实现算法统一接口的 trait，
/// 主要用于需要动态选择算法的场景。
pub trait Algorithm<Input, Output> {
    /// 执行算法
    fn execute(&self, input: Input) -> Output;
    /// 算法名称
    fn name(&self) -> &'static str;
    /// 算法描述
    fn description(&self) -> &'static str;
}

/// 排序算法 trait
///
/// 定义排序算法的统一接口
pub trait SortAlgorithm<T: Ord> {
    /// 对切片进行排序
    fn sort(&self, data: &mut [T]);
    /// 算法是否稳定
    fn is_stable(&self) -> bool;
    /// 空间复杂度描述
    fn space_complexity(&self) -> &'static str;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_display() {
        let err = AlgorithmError::NotFound;
        assert_eq!(format!("{}", err), "Element not found");

        let err = AlgorithmError::InvalidInput("test".to_string());
        assert!(format!("{}", err).contains("Invalid input"));
    }
}
