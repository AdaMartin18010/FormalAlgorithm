//! # 工程级算法实现库
//!
//! 提供10个核心算法的工程级实现，包含完整的文档、单元测试和性能基准测试。
//!
//! ## 算法清单
//!
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 归并排序 | [`merge_sort`] | O(n log n) | O(n) |
//! | 快速排序 | [`quick_sort`] | O(n log n) 平均 | O(log n) |
//! | 堆排序 | [`heap_sort`] | O(n log n) | O(1) |
//! | 二分搜索 | [`binary_search`] | O(log n) | O(1) |
//! | Dijkstra | [`dijkstra`] | O((V+E) log V) | O(V) |
//! | LCS | [`lcs`] | O(mn) | O(mn) |
//! | 活动选择 | [`greedy_activity_selection`] | O(n log n) | O(n) |
//! | 最近点对 | [`divide_conquer`] | O(n log n) | O(n) |
//! | N皇后 | [`backtracking_nqueens`] | O(N!) | O(N) |
//! | BFS/DFS | [`graph_bfs_dfs`] | O(V+E) | O(V) |

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
    IndexOutOfBounds { index: usize, len: usize },
    /// 图相关错误
    #[error("Graph error: {0}")]
    GraphError(String),
    /// 未实现
    #[error("Not implemented: {0}")]
    NotImplemented(String),
}

/// 搜索结果类型
pub type SearchResult<T> = Result<T, AlgorithmError>;

/// 归并排序模块
pub mod merge_sort;
/// 快速排序模块
pub mod quick_sort;
/// 二分搜索模块
pub mod binary_search;
/// Dijkstra算法模块
pub mod dijkstra;
/// 最长公共子序列模块
pub mod lcs;
/// 贪心算法 - 活动选择模块
pub mod greedy_activity_selection;
/// 分治算法 - 最近点对模块
pub mod divide_conquer;
/// 回溯算法 - N皇后模块
pub mod backtracking_nqueens;
/// 图遍历算法 - BFS/DFS模块
pub mod graph_bfs_dfs;
/// 堆排序模块
pub mod heap_sort;

// 重新导出主要类型和函数
pub use backtracking_nqueens::solve_n_queens;
pub use binary_search::binary_search;
pub use binary_search::lower_bound;
pub use binary_search::upper_bound;
pub use dijkstra::dijkstra;
pub use divide_conquer::closest_pair;
pub use divide_conquer::Point;
pub use graph_bfs_dfs::{bfs, dfs};
pub use greedy_activity_selection::greedy_activity_selection;
pub use greedy_activity_selection::Activity;
pub use heap_sort::heap_sort;
pub use lcs::lcs;
pub use lcs::lcs_length;
pub use merge_sort::merge_sort;
pub use quick_sort::quick_sort;

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
