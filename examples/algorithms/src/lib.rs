//! # 形式化算法实现示例 / Formal Algorithm Implementation Examples
//!
//! 本库包含经典算法的Rust实现，每个实现都对应项目文档中的形式化定义。
//!
//! This library contains Rust implementations of classic algorithms,
//! each corresponding to formal definitions in the project documentation.

pub mod sorting;
pub mod searching;
pub mod dynamic_programming;
pub mod graph;

// Re-export commonly used items
pub use sorting::{merge_sort, quick_sort};
pub use searching::binary_search;
pub use dynamic_programming::longest_common_subsequence;
pub use graph::dijkstra;

