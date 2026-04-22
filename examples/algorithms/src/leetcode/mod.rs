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
