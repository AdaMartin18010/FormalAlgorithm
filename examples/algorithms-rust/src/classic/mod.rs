//! 经典算法模块
//!
//! 包含排序、搜索、图算法、动态规划、数据结构等核心算法实现。


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
/// 蚁群优化模块
pub mod ant_colony;
/// 禁忌搜索模块
pub mod tabu_search;