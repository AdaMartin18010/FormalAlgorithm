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
//!
//! ### 图算法扩展 (3个)
//! | 算法 | 模块 | 时间复杂度 | 空间复杂度 |
//! |------|------|-----------|-----------|
//! | 拓扑排序 | [`topological_sort`] | O(V+E) | O(V) |
//! | 强连通分量 | [`strongly_connected_components`] | O(V+E) | O(V) |
//!
//! ### 高级数据结构 (5个)
//! | 数据结构 | 模块 | 操作复杂度 | 空间复杂度 |
//! |----------|------|-----------|-----------|
//! | LRU缓存 | [`lru_cache`] | get/put: O(1) | O(capacity) |
//! | 一致性哈希 | [`consistent_hash`] | get: O(log N) | O(N×V) |
//! | 布隆过滤器 | [`bloom_filter`] | insert/contains: O(k) | O(m) |
//! | 线段树 | [`segment_tree`] | update/query: O(log n) | O(n) |
//! | 树状数组 | [`fenwick_tree`] | update/query: O(log n) | O(n) |
//! | 后缀数组 | [`suffix_array`] | build: O(n log n) | O(n) |

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
/// 插入排序模块
pub mod insertion_sort;
/// 选择排序模块
pub mod selection_sort;
/// 冒泡排序模块
pub mod bubble_sort;
/// 0/1背包问题模块
pub mod knapsack;
/// 最长递增子序列模块
pub mod longest_increasing_subsequence;
/// 硬币找零问题模块
pub mod coin_change;

// 搜索算法模块
/// 二分搜索模块
pub mod binary_search;

// 图算法模块
/// Dijkstra算法模块
pub mod dijkstra;
/// A*搜索算法模块
pub mod astar;
/// 二叉堆与优先队列模块
pub mod binary_heap;
/// 二叉搜索树模块
pub mod binary_search_tree;
/// KMP字符串匹配模块
pub mod kmp;
/// Median of Medians选择算法模块
pub mod median_of_medians;
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

// 图算法扩展模块
/// 拓扑排序模块 (Kahn算法、DFS)
pub mod topological_sort;
/// 强连通分量模块 (Kosaraju、Tarjan)
pub mod strongly_connected_components;
/// Tarjan强连通分量算法
pub mod tarjan_scc;
/// Kosaraju强连通分量算法
pub mod kosaraju_scc;
/// 割点/关节点算法
pub mod articulation_points;
/// 桥边算法
pub mod bridges;
/// 欧拉路径/回路算法
pub mod euler_tour;
/// 二分图匹配（匈牙利算法）
pub mod bipartite_matching;

// 高级数据结构模块
/// LRU缓存模块
pub mod lru_cache;
/// 一致性哈希模块
pub mod consistent_hash;
/// 布隆过滤器模块
pub mod bloom_filter;
/// 线段树模块
pub mod segment_tree;
/// 树状数组模块
pub mod fenwick_tree;
/// 后缀数组模块
pub mod suffix_array;
/// van Emde Boas 树模块
pub mod van_emde_boas;
/// 树上并查集模块 (DSU on Tree)
pub mod dsu_on_tree;
/// 莫算法模块 (Mo's Algorithm)
pub mod mo_algorithm;
/// 树链剖分模块 (Heavy-Light Decomposition)
pub mod heavy_light_decomposition;
/// 点分治模块 (Centroid Decomposition)
pub mod centroid_decomposition;
/// 后缀自动机模块 (Suffix Automaton)
pub mod suffix_automaton;
/// 斐波那契堆模块 (Fibonacci Heap)
pub mod fibonacci_heap;
// 跳表模块 - 当前实现有内存安全问题，暂时禁用
pub mod skiplist;

// 数值算法模块
/// 矩阵操作模块（Strassen、快速幂、高斯消元）
pub mod matrix_operations;
/// 多项式运算模块（求值、插值、FFT）
pub mod polynomial;
/// 几何工具模块（凸包、旋转卡壳）
pub mod geometry_utils;
/// 离散对数模块（BSGS、Pollard's Rho）
pub mod discrete_log;
/// 素性测试模块（Miller-Rabin、因数分解）
pub mod primality_test;

// 网络流算法
/// 最小费用最大流模块
pub mod min_cost_max_flow;

// 逻辑求解模块
/// 2-SAT求解器模块
pub mod sat2;

// 字符串算法
/// 滚动哈希模块
pub mod rolling_hash;

// 高级数据结构
/// 可持久化线段树模块
pub mod persistent_segment_tree;
// 精确覆盖算法
/// 舞蹈链模块（DLX）
pub mod dancing_links;

// 启发式算法
/// 模拟退火算法模块
pub mod simulated_annealing;

// 基础数据结构 (Foundation Data Structures)
/// 动态数组模块
pub mod dynamic_array;
/// 链表模块
pub mod linked_list;
/// 栈模块
pub mod stack;
/// 队列模块
pub mod queue;
/// 双端队列模块
pub mod deque;
/// 哈希表模块
pub mod hash_table;
/// 并查集模块
pub mod union_find;
/// 红黑树模块
pub mod red_black_tree;
/// AVL树模块
pub mod avl_tree;
/// B树模块
pub mod b_tree;
/// Splay树模块
pub mod splay_tree;
// 跳表模块 - 当前实现有内存安全问题，暂时禁用
// pub mod skiplist;

// 树型高级数据结构
/// 笛卡尔树模块
pub mod cartesian_tree;
/// 区间树模块
pub mod interval_tree;
/// Trie树模块
pub mod trie;
/// 二维树状数组模块
pub mod binary_indexed_tree_2d;

// 排序与搜索扩展
/// 综合排序算法模块
pub mod sorting;
/// 计数排序模块
pub mod counting_sort;
/// 基数排序模块
pub mod radix_sort;
/// 桶排序模块
pub mod bucket_sort;
/// 快速选择模块
pub mod quick_select;

// 图算法扩展
/// 最小生成树模块
pub mod graph_mst;
/// Bellman-Ford最短路径模块
pub mod bellman_ford;
/// Floyd-Warshall全源最短路径模块
pub mod floyd_warshall;
/// Johnson全源最短路径模块
pub mod johnson;
/// Hopcroft-Karp二分图匹配模块
pub mod hopcroft_karp;

// 字符串算法扩展
/// Rabin-Karp字符串匹配模块
pub mod rabin_karp;
/// Z算法模块
pub mod z_algorithm;
/// Manacher回文算法模块
pub mod manacher;
/// AC自动机模块
pub mod ac_automaton;

// 数值与矩阵算法
/// 矩阵链乘法模块
pub mod matrix_chain;
/// 最优二叉搜索树模块
pub mod optimal_bst;
/// 最近点对模块
pub mod closest_pair;
/// 快速傅里叶变换模块
pub mod fft;
/// 扩展欧几里得算法模块
pub mod extended_euclidean;
/// 中国剩余定理模块
pub mod chinese_remainder;
/// LUP 分解模块
pub mod lup_decomposition;

// 启发式算法扩展
/// 遗传算法模块
pub mod genetic_algorithm;

// 排序算法
pub use heap_sort::heap_sort;
pub use merge_sort::merge_sort;
pub use quick_sort::quick_sort;
pub use insertion_sort::insertion_sort;
pub use selection_sort::selection_sort;
pub use bubble_sort::bubble_sort;
pub use binary_heap::{BinaryHeap, MinHeap, build_max_heap};
pub use knapsack::{knapsack_01, unbounded_knapsack, fractional_knapsack};
pub use longest_increasing_subsequence::{lis_length_dp, lis_length_binary, lis_dp, lis_binary};
pub use coin_change::{coin_change_min, coin_change_ways};
pub use binary_search_tree::BinarySearchTree;
pub use kmp::kmp_search;
pub use median_of_medians::{select, median};

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

// 图算法扩展
pub use topological_sort::{
    topological_sort_kahn, topological_sort_dfs, has_cycle, TopologicalSortResult
};
pub use strongly_connected_components::{
    kosaraju, tarjan, is_strongly_connected, SCCResult
};
pub use tarjan_scc::{tarjan_scc, TarjanSCCResult};
pub use kosaraju_scc::{kosaraju_scc, KosarajuSCCResult};
pub use articulation_points::{find_articulation_points, ArticulationPointResult};
pub use bridges::{find_bridges, BridgeResult, Edge};
pub use euler_tour::{
    find_eulerian_circuit_undirected, find_eulerian_path_undirected,
    find_eulerian_circuit_directed, find_eulerian_path_directed,
    has_eulerian_circuit_undirected, has_eulerian_path_undirected,
    EulerResult
};
pub use bipartite_matching::{
    hungarian_dfs, hungarian_bfs, is_bipartite, bipartite_partition,
    MatchingResult, max_matching_size
};

// 高级数据结构
pub use lru_cache::LruCache;
pub use consistent_hash::ConsistentHash;
pub use bloom_filter::BloomFilter;
pub use segment_tree::{SegmentTree, LazySegmentTree};
pub use fenwick_tree::{FenwickTree, RangeUpdateFenwickTree, count_inversions};
pub use suffix_array::SuffixArray;
pub use van_emde_boas::VanEmdeBoasTree;
pub use dsu_on_tree::DsuOnTree;
pub use mo_algorithm::MoAlgorithm;
pub use heavy_light_decomposition::HeavyLightDecompositionWithSegTree;
pub use centroid_decomposition::CentroidDecomposition;
pub use suffix_automaton::SuffixAutomaton;
pub use fibonacci_heap::FibonacciHeap;
pub use fibonacci_heap::NodeHandle;
pub use skiplist::SkipList;

// 数值算法
pub use matrix_operations::Matrix as Mat;
pub use polynomial::{Polynomial, lagrange_interpolate, lagrange_polynomial, NewtonInterpolation, fft_multiply};
pub use geometry_utils::{Point as GeoPoint, Segment, Line, Circle, Polygon, convex_hull, 
    rotating_calipers_diameter, rotating_calipers_width, closest_pair as closest_pair_geo};
pub use discrete_log::{bsgs, ex_bsgs, pollard_rho_dlog, pollard_rho_factor, factorize as dlog_factorize, pohlig_hellman};
pub use primality_test::{is_probable_prime, is_prime_deterministic, pollard_rho as rho_factor, factorize as prime_factorize,
    prime_factorization, euler_totient, mobius, sieve_of_eratosthenes, linear_sieve, 
    nth_prime, next_prime, prev_prime};

// 网络流算法
pub use min_cost_max_flow::{MinCostMaxFlow, MCMFResult, min_cost_max_flow_spfa, min_cost_max_flow_dijkstra};

// 2-SAT求解
pub use sat2::{Solver2Sat, Sat2Result, solve_2sat};

// 滚动哈希
pub use rolling_hash::{RollingHash, MultiRollingHash, HashPair, rolling_hash, double_hash};

// 可持久化线段树
pub use persistent_segment_tree::{PersistentSegmentTree, KthPersistentSegmentTree, QueryResult, persistent_segment_tree};

// 舞蹈链
pub use dancing_links::{DancingLinks, DLXResult, exact_cover, exact_cover_all};

// 模拟退火
pub use simulated_annealing::{SimulatedAnnealing, SAResult, TspSolver, FunctionOptimizer, SchedulingSolver};

// 基础数据结构
pub use union_find::UnionFind;
pub use dynamic_array::DynamicArray;
pub use linked_list::{SinglyLinkedList, DoublyLinkedList, CircularLinkedList};
pub use stack::Stack;
pub use queue::{Queue, QueueWithTwoStacks};
pub use deque::Deque;
pub use hash_table::{HashTableSeparateChaining, HashTableOpenAddressing};
pub use red_black_tree::RedBlackTree;
pub use avl_tree::AVLTree;
pub use b_tree::BTree;
pub use splay_tree::SplayTree;
pub use cartesian_tree::CartesianTree;
pub use interval_tree::{IntervalTree, Interval, IntervalSet};
pub use trie::{Trie, TrieNode, BinaryTrie};
pub use binary_indexed_tree_2d::BIT2D;

// 排序与搜索扩展
pub use counting_sort::counting_sort;
pub use radix_sort::radix_sort;
pub use bucket_sort::bucket_sort;
pub use quick_select::quick_select;
// pub use sorting::...; // 独立模块已提供相同导出

// 图算法扩展
pub use graph_mst::{Edge as MSTEdge, kruskal, prim, prim_adj_list};

// 字符串算法扩展
pub use rabin_karp::{RabinKarp, RabinKarp2D};
pub use z_algorithm::{z_algorithm, z_search, z_count};
pub use manacher::{manacher, longest_palindrome, count_palindromes};
pub use ac_automaton::ACAutomaton;

// 数值与矩阵算法
pub use matrix_chain::{MatrixChain, OptimalSolution};
pub use optimal_bst::{OptimalBST, OptimalBSTResult, SimpleOptimalBST};
pub use closest_pair::{Point as ClosestPoint, ClosestPairResult, closest_pair as closest_pair_optimal, closest_pair_brute_force};
pub use fft::{fft, ifft, polynomial_multiply};
pub use genetic_algorithm::{GeneticAlgorithm, SelectionMethod};

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
