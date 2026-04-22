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

// === 双指针专题 ===
/// LeetCode 11. 盛最多水的容器（对撞指针）
pub mod lc0011_container_with_most_water;
/// LeetCode 15. 三数之和（对撞指针）
pub mod lc0015_3sum;
/// LeetCode 142. 环形链表 II（快慢指针 / Floyd 判环）
pub mod lc0142_linked_list_cycle_ii;

// === 滑动窗口专题 ===
/// LeetCode 3. 无重复字符的最长子串（变长滑动窗口）
pub mod lc0003_longest_substring_without_repeating_characters;
/// LeetCode 76. 最小覆盖子串（滑动窗口 + 双哈希表）
pub mod lc0076_minimum_window_substring;
/// LeetCode 239. 滑动窗口最大值（单调队列优化）
pub mod lc0239_sliding_window_maximum;

// === 动态规划专题 ===
/// LeetCode 72. 编辑距离（双串 DP）
pub mod lc0072_edit_distance;
/// LeetCode 198. 打家劫舍（线性 DP）
pub mod lc0198_house_robber;

// === 链表专题 ===
/// LeetCode 21. 合并两个有序链表（递归 / 迭代）
pub mod lc0021_merge_two_sorted_lists;
/// LeetCode 136. 只出现一次的数字（异或群论）
pub mod lc0136_single_number;

// === 回溯与 DFS 专题 ===
/// LeetCode 46. 全排列（排列树回溯）
pub mod lc0046_permutations;

// === BFS 与图搜索专题 ===
/// LeetCode 127. 单词接龙（双向 BFS）
pub mod lc0127_word_ladder;
/// LeetCode 994. 腐烂的橘子（多源 BFS）
pub mod lc0994_rotting_oranges;

// === 图论专题 ===
/// LeetCode 133. 克隆图（DFS/BFS + 哈希映射）
pub mod lc0133_clone_graph;
/// LeetCode 200. 岛屿数量（DFS Flood Fill）
pub mod lc0200_number_of_islands;
/// LeetCode 207. 课程表（拓扑排序 / Kahn 算法）
pub mod lc0207_course_schedule;
/// LeetCode 210. 课程表 II（拓扑排序输出）
pub mod lc0210_course_schedule_ii;
/// LeetCode 743. 网络延迟时间（Dijkstra 单源最短路）
pub mod lc0743_network_delay_time;
/// LeetCode 787. K站中转内最便宜的航班（Bellman-Ford）
pub mod lc0787_cheapest_flights_within_k_stops;
/// LeetCode 1584. 连接所有点的最小费用（Prim MST）
pub mod lc1584_min_cost_to_connect_all_points;

// === 剑指 Offer 专题 ===
/// 剑指 Offer 10-I. 斐波那契数列
#[path = "剑指Offer_10_I_斐波那契数列.rs"]
pub mod jianzhi_offer_10_i_fibonacci;

// === 前缀和与差分专题 ===
/// LeetCode 560. 和为 K 的子数组（前缀和 + 哈希表）
pub mod lc0560_subarray_sum_equals_k;
/// LeetCode 523. 连续的子数组和（前缀和 + 同余定理）
pub mod lc0523_continuous_subarray_sum;
/// LeetCode 370. 区间加法（差分数组）
pub mod lc0370_range_addition;

// === 分治专题 ===
/// LeetCode 912. 排序数组（归并排序）
pub mod lc0912_sort_an_array;
/// LeetCode 23. 合并 K 个升序链表（分治合并）
pub mod lc0023_merge_k_sorted_lists;
/// LeetCode 4. 寻找两个正序数组的中位数（二分/分治混合）
pub mod lc0004_median_of_two_sorted_arrays;

// === 贪心算法专题 ===
/// LeetCode 455. 分发饼干（贪心 + 排序）
pub mod lc0455_assign_cookies;
/// LeetCode 55. 跳跃游戏（贪心可达性）
pub mod lc0055_jump_game;
/// LeetCode 45. 跳跃游戏 II（贪心最少步数）
pub mod lc0045_jump_game_ii;
/// LeetCode 435. 无重叠区间（贪心区间调度）
pub mod lc0435_non_overlapping_intervals;

// 重新导出主要函数以方便使用
pub use lc0704_binary_search::search as lc0704_search;
pub use lc0033_search_in_rotated_sorted_array::search as lc0033_search;
pub use lc0153_find_minimum_in_rotated_sorted_array::find_min as lc0153_find_min;
pub use lc0072_edit_distance::min_distance as lc0072_min_distance;
pub use lc0198_house_robber::rob as lc0198_rob;
// pub use lc0136_single_number::single_number as lc0136_single_number;

// === 数学专题 ===
/// LeetCode 9. 回文数（数字反转 + 溢出避免）
pub mod lc0009_palindrome_number;
/// LeetCode 50. Pow(x, n)（快速幂 / 二进制分解）
pub mod lc0050_powx_n;
/// LeetCode 204. 计数质数（埃氏筛）
pub mod lc0204_count_primes;
/// LeetCode 96. 不同的二叉搜索树（卡特兰数 DP）
pub mod lc0096_unique_binary_search_trees;
// === 数组与哈希表专题 ===
/// LeetCode 1. 两数之和（哈希表）
pub mod lc0001_two_sum;
/// LeetCode 26. 删除有序数组中的重复项（双指针）
pub mod lc0026_remove_duplicates;
/// LeetCode 48. 旋转图像（矩阵转置 + 翻转）
pub mod lc0048_rotate_image;

// === 字符串专题 ===
/// LeetCode 5. 最长回文子串（中心扩展 / Manacher）
pub mod lc0005_longest_palindromic_substring;
/// LeetCode 17. 电话号码的字母组合（回溯）
pub mod lc0017_letter_combinations;
/// LeetCode 28. 实现 strStr()（KMP / Sunday）
pub mod lc0028_implement_strstr;
/// LeetCode 214. 最短回文串（KMP 前缀函数）
pub mod lc0214_shortest_palindrome;
/// LeetCode 516. 最长回文子序列（区间 DP）
pub mod lc0516_longest_palindromic_subsequence;
/// LeetCode 583. 两个字符串的删除操作（双串 DP）
pub mod lc0583_delete_operation_for_two_strings;
/// LeetCode 647. 回文子串（中心扩展）
pub mod lc0647_palindromic_substrings;
/// LeetCode 1143. 最长公共子序列（经典双串 DP）
pub mod lc1143_longest_common_subsequence;

// === 栈与队列专题 ===
/// LeetCode 20. 有效的括号（栈匹配）
pub mod lc0020_valid_parentheses;
/// LeetCode 155. 最小栈（辅助栈同步最小值）
pub mod lc0155_min_stack;
/// LeetCode 232. 用栈实现队列（双栈模拟）
pub mod lc0232_implement_queue_using_stacks;

// === 链表专题 ===
/// LeetCode 141. 环形链表（快慢指针 / Floyd 判环）
pub mod lc0141_linked_list_cycle;
/// LeetCode 206. 反转链表（迭代 / 递归）
pub mod lc0206_reverse_linked_list;

// === 树专题 ===
/// LeetCode 94. 二叉树的中序遍历（Morris / 栈）
pub mod lc0094_binary_tree_inorder_traversal;
/// LeetCode 102. 二叉树的层序遍历（BFS）
pub mod lc0102_binary_tree_level_order;
/// LeetCode 104. 二叉树的最大深度（DFS / BFS）
pub mod lc0104_maximum_depth_of_binary_tree;
/// LeetCode 226. 翻转二叉树（递归 / 迭代）
pub mod lc0226_invert_binary_tree;
/// LeetCode 236. 二叉树的最近公共祖先（DFS / 后序遍历）
pub mod lc0236_lowest_common_ancestor;

// === 回溯与 DFS 专题 ===
/// LeetCode 37. 解数独（回溯 + 剪枝）
pub mod lc0037_sudoku_solver;
/// LeetCode 39. 组合总和（回溯 + 剪枝）
pub mod lc0039_combination_sum;
/// LeetCode 51. N 皇后（排列树回溯）
pub mod lc0051_n_queens;

// === 动态规划专题 ===
/// LeetCode 62. 不同路径（组合数学 / DP）
pub mod lc0062_unique_paths;
/// LeetCode 70. 爬楼梯（线性 DP / 斐波那契）
pub mod lc0070_climbing_stairs;
/// LeetCode 300. 最长递增子序列（DP + 二分优化）
pub mod lc0300_longest_increasing_subsequence;
/// LeetCode 312. 戳气球（区间 DP）
pub mod lc0312_burst_balloons;
/// LeetCode 416. 分割等和子集（0-1 背包 DP）
pub mod lc0416_partition_equal_subset_sum;

// === 滑动窗口 / 前缀和专题 ===
/// LeetCode 209. 长度最小的子数组（滑动窗口 / 前缀和）
pub mod lc0209_minimum_size_subarray_sum;

// === 数学专题 ===
/// LeetCode 223. 矩形面积（几何 / 容斥原理）
pub mod lc0223_rectangle_area;
/// LeetCode 372. 超级次方（快速幂 / 模运算）
pub mod lc0372_super_pow;
/// LeetCode 384. 打乱数组（Fisher-Yates 洗牌）
pub mod lc0384_shuffle_an_array;
/// LeetCode 398. 随机数索引（蓄水池抽样）
pub mod lc0398_random_pick_index;
/// LeetCode 470. 用 Rand7() 实现 Rand10()（拒绝采样）
pub mod lc0470_rand10_using_rand7;
/// LeetCode 587. 安装栅栏（凸包 / Graham 扫描）
pub mod lc0587_erect_the_fence;
