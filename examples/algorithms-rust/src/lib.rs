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
/// 快速排序模块
/// 堆排序模块
/// 插入排序模块
/// 选择排序模块
/// 冒泡排序模块
/// 0/1背包问题模块
/// 最长递增子序列模块
/// 硬币找零问题模块

// 搜索算法模块
/// 二分搜索模块

// 图算法模块
/// Dijkstra算法模块
/// A*搜索算法模块
/// 二叉堆与优先队列模块
/// 二叉搜索树模块
/// KMP字符串匹配模块
/// Median of Medians选择算法模块
/// 图遍历算法 - BFS/DFS模块

// 动态规划模块
/// 最长公共子序列模块

// 贪心算法模块
/// 贪心算法 - 活动选择模块

// 回溯算法模块
/// 回溯算法 - N皇后模块
/// 回溯算法 - 通用回溯模块

// 分治算法模块
/// 分治算法模块

// 图算法扩展模块
/// 拓扑排序模块 (Kahn算法、DFS)
/// 强连通分量模块 (Kosaraju、Tarjan)
/// Tarjan强连通分量算法
/// Kosaraju强连通分量算法
/// 割点/关节点算法
/// 桥边算法
/// 欧拉路径/回路算法
/// 二分图匹配（匈牙利算法）

// 高级数据结构模块
/// LRU缓存模块
/// 一致性哈希模块
/// 布隆过滤器模块
/// 线段树模块
/// 树状数组模块
/// 后缀数组模块
/// van Emde Boas 树模块
/// 树上并查集模块 (DSU on Tree)
/// 莫算法模块 (Mo's Algorithm)
/// 树链剖分模块 (Heavy-Light Decomposition)
/// 点分治模块 (Centroid Decomposition)
/// 后缀自动机模块 (Suffix Automaton)
/// 斐波那契堆模块 (Fibonacci Heap)
// 跳表模块 - 当前实现有内存安全问题，暂时禁用

// 数值算法模块
/// 矩阵操作模块（Strassen、快速幂、高斯消元）
/// 多项式运算模块（求值、插值、FFT）
/// 几何工具模块（凸包、旋转卡壳）
/// 离散对数模块（BSGS、Pollard's Rho）
/// 素性测试模块（Miller-Rabin、因数分解）

// 网络流算法
/// 最小费用最大流模块

// 逻辑求解模块
/// 2-SAT求解器模块

// 字符串算法
/// 滚动哈希模块

// 高级数据结构
/// 可持久化线段树模块
// 精确覆盖算法
/// 舞蹈链模块（DLX）

// 启发式算法
/// 模拟退火算法模块

// LeetCode 经典题目模块
/// LeetCode 算法实现模块
pub mod classic;
/// LeetCode 经典题目模块
pub mod leetcode;

// 基础数据结构 (Foundation Data Structures)
/// 动态数组模块
/// 链表模块
/// 栈模块
/// 队列模块
/// 双端队列模块
/// 哈希表模块
/// 并查集模块
/// 红黑树模块
/// AVL树模块
/// B树模块
/// Splay树模块
// 跳表模块 - 当前实现有内存安全问题，暂时禁用
// pub mod skiplist;

// 树型高级数据结构
/// 笛卡尔树模块
/// 区间树模块
/// Trie树模块
/// 二维树状数组模块

// 排序与搜索扩展
/// 综合排序算法模块
/// 计数排序模块
/// 基数排序模块
/// 桶排序模块
/// 快速选择模块

// 图算法扩展
/// 最小生成树模块
/// Bellman-Ford最短路径模块
/// Floyd-Warshall全源最短路径模块
/// Johnson全源最短路径模块
/// Hopcroft-Karp二分图匹配模块

// 字符串算法扩展
/// Rabin-Karp字符串匹配模块
/// Z算法模块
/// Manacher回文算法模块
/// AC自动机模块

// 数值与矩阵算法
/// 矩阵链乘法模块
/// 最优二叉搜索树模块
/// 最近点对模块
/// 快速傅里叶变换模块
/// 扩展欧几里得算法模块
/// 中国剩余定理模块
/// LUP 分解模块

// 启发式算法扩展
/// 遗传算法模块
/// 蚁群优化模块
/// 禁忌搜索模块

// 排序算法
pub use classic::heap_sort::heap_sort;
pub use classic::merge_sort::merge_sort;
pub use classic::quick_sort::quick_sort;
pub use classic::insertion_sort::insertion_sort;
pub use classic::selection_sort::selection_sort;
pub use classic::bubble_sort::bubble_sort;
pub use classic::binary_heap::{BinaryHeap, MinHeap, build_max_heap};
pub use classic::knapsack::{knapsack_01, unbounded_knapsack, fractional_knapsack};
pub use classic::longest_increasing_subsequence::{lis_length_dp, lis_length_binary, lis_dp, lis_binary};
pub use classic::coin_change::{coin_change_min, coin_change_ways};
pub use classic::binary_search_tree::BinarySearchTree;
pub use classic::kmp::kmp_search;
pub use classic::median_of_medians::{select, median};

// 搜索算法
pub use classic::binary_search::binary_search;
pub use classic::binary_search::{lower_bound, upper_bound};

// 图算法
pub use classic::dijkstra::dijkstra;
pub use classic::graph_bfs_dfs::{bfs, dfs};

// 动态规划
pub use classic::lcs::lcs;
pub use classic::lcs::lcs_length;

// 贪心算法
pub use classic::greedy_activity_selection::greedy_activity_selection;
pub use classic::greedy_activity_selection::Activity;

// 回溯算法
pub use classic::backtracking_nqueens::solve_n_queens;
pub use classic::backtracking::{subset_sum, graph_coloring, generate_permutations};

// 分治算法
pub use classic::divide_and_conquer::{closest_pair, Point, Matrix, strassen_multiply};

// 图算法扩展
pub use classic::topological_sort::{
    topological_sort_kahn, topological_sort_dfs, has_cycle, TopologicalSortResult
};
pub use classic::strongly_connected_components::{
    kosaraju, tarjan, is_strongly_connected, SCCResult
};
pub use classic::tarjan_scc::{tarjan_scc, TarjanSCCResult};
pub use classic::kosaraju_scc::{kosaraju_scc, KosarajuSCCResult};
pub use classic::articulation_points::{find_articulation_points, ArticulationPointResult};
pub use classic::bridges::{find_bridges, BridgeResult, Edge};
pub use classic::euler_tour::{
    find_eulerian_circuit_undirected, find_eulerian_path_undirected,
    find_eulerian_circuit_directed, find_eulerian_path_directed,
    has_eulerian_circuit_undirected, has_eulerian_path_undirected,
    EulerResult
};
pub use classic::bipartite_matching::{
    hungarian_dfs, hungarian_bfs, is_bipartite, bipartite_partition,
    MatchingResult, max_matching_size
};

// 高级数据结构
pub use classic::lru_cache::LruCache;
pub use classic::consistent_hash::ConsistentHash;
pub use classic::bloom_filter::BloomFilter;
pub use classic::segment_tree::{SegmentTree, LazySegmentTree};
pub use classic::fenwick_tree::{FenwickTree, RangeUpdateFenwickTree, count_inversions};
pub use classic::suffix_array::SuffixArray;
pub use classic::van_emde_boas::VanEmdeBoasTree;
pub use classic::dsu_on_tree::DsuOnTree;
pub use classic::mo_algorithm::MoAlgorithm;
pub use classic::heavy_light_decomposition::HeavyLightDecompositionWithSegTree;
pub use classic::centroid_decomposition::CentroidDecomposition;
pub use classic::suffix_automaton::SuffixAutomaton;
pub use classic::fibonacci_heap::FibonacciHeap;
pub use classic::fibonacci_heap::NodeHandle;
pub use classic::skiplist::SkipList;

// 数值算法
pub use classic::matrix_operations::Matrix as Mat;
pub use classic::polynomial::{Polynomial, lagrange_interpolate, lagrange_polynomial, NewtonInterpolation, fft_multiply};
pub use classic::geometry_utils::{Point as GeoPoint, Segment, Line, Circle, Polygon, convex_hull, 
    rotating_calipers_diameter, rotating_calipers_width, closest_pair as closest_pair_geo};
pub use classic::discrete_log::{bsgs, ex_bsgs, pollard_rho_dlog, pollard_rho_factor, factorize as dlog_factorize, pohlig_hellman};
pub use classic::primality_test::{is_probable_prime, is_prime_deterministic, pollard_rho as rho_factor, factorize as prime_factorize,
    prime_factorization, euler_totient, mobius, sieve_of_eratosthenes, linear_sieve, 
    nth_prime, next_prime, prev_prime};

// 网络流算法
pub use classic::min_cost_max_flow::{MinCostMaxFlow, MCMFResult, min_cost_max_flow_spfa, min_cost_max_flow_dijkstra};

// 2-SAT求解
pub use classic::sat2::{Solver2Sat, Sat2Result, solve_2sat};

// 滚动哈希
pub use classic::rolling_hash::{RollingHash, MultiRollingHash, HashPair, rolling_hash, double_hash};

// 可持久化线段树
pub use classic::persistent_segment_tree::{PersistentSegmentTree, KthPersistentSegmentTree, QueryResult, persistent_segment_tree};

// 舞蹈链
pub use classic::dancing_links::{DancingLinks, DLXResult, exact_cover, exact_cover_all};

// 模拟退火
pub use classic::simulated_annealing::{SimulatedAnnealing, SAResult, TspSolver, FunctionOptimizer, SchedulingSolver};

// 基础数据结构
pub use classic::union_find::UnionFind;
pub use classic::dynamic_array::DynamicArray;
pub use classic::linked_list::{SinglyLinkedList, DoublyLinkedList, CircularLinkedList};
pub use classic::stack::Stack;
pub use classic::queue::{Queue, QueueWithTwoStacks};
pub use classic::deque::Deque;
pub use classic::hash_table::{HashTableSeparateChaining, HashTableOpenAddressing};
pub use classic::red_black_tree::RedBlackTree;
pub use classic::avl_tree::AVLTree;
pub use classic::b_tree::BTree;
pub use classic::splay_tree::SplayTree;
pub use classic::cartesian_tree::CartesianTree;
pub use classic::interval_tree::{IntervalTree, Interval, IntervalSet};
pub use classic::trie::{Trie, TrieNode, BinaryTrie};
pub use classic::binary_indexed_tree_2d::BIT2D;

// 排序与搜索扩展
pub use classic::counting_sort::counting_sort;
pub use classic::radix_sort::radix_sort;
pub use classic::bucket_sort::bucket_sort;
pub use classic::quick_select::quick_select;
// pub use classic::sorting::...; // 独立模块已提供相同导出

// 图算法扩展
pub use classic::graph_mst::{Edge as MSTEdge, kruskal, prim, prim_adj_list};

// 字符串算法扩展
pub use classic::rabin_karp::{RabinKarp, RabinKarp2D};
pub use classic::z_algorithm::{z_algorithm, z_search, z_count};
pub use classic::manacher::{manacher, longest_palindrome, count_palindromes};
pub use classic::ac_automaton::ACAutomaton;

// 数值与矩阵算法
pub use classic::matrix_chain::{MatrixChain, OptimalSolution};
pub use classic::optimal_bst::{OptimalBST, OptimalBSTResult, SimpleOptimalBST};
pub use classic::closest_pair::{Point as ClosestPoint, ClosestPairResult, closest_pair as closest_pair_optimal, closest_pair_brute_force};
pub use classic::fft::{fft, ifft, polynomial_multiply};
pub use classic::genetic_algorithm::{GeneticAlgorithm, SelectionMethod};
pub use classic::ant_colony::{aco_tsp, TspGraph};
pub use classic::tabu_search::{tabu_search, tabu_sort};

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
