//! LeetCode 经典题目实现
//!
//! 本模块提供 LeetCode 高频题目的工程级 Rust 实现，
//! 包含完整的形式化规约、循环不变式、复杂度分析与单元测试。
//!
//! 交叉引用：
//! - 算法面试专题：docs/13-LeetCode算法面试专题/
//! - 形式化证明：docs/03-形式化证明/
//! - 复杂度理论：docs/04-算法复杂度/
//!
//! ## 组织变更说明
//! 自 v3.4.0 起，所有 LeetCode 实现已迁移到 examples/by-algorithm/lcXXXX/rust/ 目录，
//! 采用 Rosetta Code 模式（按算法组织）。本模块通过 #[path] 属性保持向后兼容。

#[path = "../../../by-algorithm/lc0001/rust/lc0001_two_sum.rs"]
pub mod lc0001_two_sum;

#[path = "../../../by-algorithm/lc0003/rust/lc0003_longest_substring_without_repeating_characters.rs"]
pub mod lc0003_longest_substring_without_repeating_characters;

#[path = "../../../by-algorithm/lc0004/rust/lc0004_median_of_two_sorted_arrays.rs"]
pub mod lc0004_median_of_two_sorted_arrays;

#[path = "../../../by-algorithm/lc0005/rust/lc0005_longest_palindromic_substring.rs"]
pub mod lc0005_longest_palindromic_substring;

#[path = "../../../by-algorithm/lc0009/rust/lc0009_palindrome_number.rs"]
pub mod lc0009_palindrome_number;

#[path = "../../../by-algorithm/lc0011/rust/lc0011_container_with_most_water.rs"]
pub mod lc0011_container_with_most_water;

#[path = "../../../by-algorithm/lc0015/rust/lc0015_3sum.rs"]
pub mod lc0015_3sum;

#[path = "../../../by-algorithm/lc0017/rust/lc0017_letter_combinations.rs"]
pub mod lc0017_letter_combinations;

#[path = "../../../by-algorithm/lc0020/rust/lc0020_valid_parentheses.rs"]
pub mod lc0020_valid_parentheses;

#[path = "../../../by-algorithm/lc0021/rust/lc0021_merge_two_sorted_lists.rs"]
pub mod lc0021_merge_two_sorted_lists;

#[path = "../../../by-algorithm/lc0023/rust/lc0023_merge_k_sorted_lists.rs"]
pub mod lc0023_merge_k_sorted_lists;

#[path = "../../../by-algorithm/lc0026/rust/lc0026_remove_duplicates.rs"]
pub mod lc0026_remove_duplicates;

#[path = "../../../by-algorithm/lc0028/rust/lc0028_implement_strstr.rs"]
pub mod lc0028_implement_strstr;

#[path = "../../../by-algorithm/lc0033/rust/lc0033_search_in_rotated_sorted_array.rs"]
pub mod lc0033_search_in_rotated_sorted_array;

#[path = "../../../by-algorithm/lc0037/rust/lc0037_sudoku_solver.rs"]
pub mod lc0037_sudoku_solver;

#[path = "../../../by-algorithm/lc0039/rust/lc0039_combination_sum.rs"]
pub mod lc0039_combination_sum;

#[path = "../../../by-algorithm/lc0045/rust/lc0045_jump_game_ii.rs"]
pub mod lc0045_jump_game_ii;

#[path = "../../../by-algorithm/lc0046/rust/lc0046_permutations.rs"]
pub mod lc0046_permutations;

#[path = "../../../by-algorithm/lc0048/rust/lc0048_rotate_image.rs"]
pub mod lc0048_rotate_image;

#[path = "../../../by-algorithm/lc0050/rust/lc0050_powx_n.rs"]
pub mod lc0050_powx_n;

#[path = "../../../by-algorithm/lc0051/rust/lc0051_n_queens.rs"]
pub mod lc0051_n_queens;

#[path = "../../../by-algorithm/lc0055/rust/lc0055_jump_game.rs"]
pub mod lc0055_jump_game;

#[path = "../../../by-algorithm/lc0062/rust/lc0062_unique_paths.rs"]
pub mod lc0062_unique_paths;

#[path = "../../../by-algorithm/lc0070/rust/lc0070_climbing_stairs.rs"]
pub mod lc0070_climbing_stairs;

#[path = "../../../by-algorithm/lc0072/rust/lc0072_edit_distance.rs"]
pub mod lc0072_edit_distance;

#[path = "../../../by-algorithm/lc0076/rust/lc0076_minimum_window_substring.rs"]
pub mod lc0076_minimum_window_substring;

#[path = "../../../by-algorithm/lc0094/rust/lc0094_binary_tree_inorder_traversal.rs"]
pub mod lc0094_binary_tree_inorder_traversal;

#[path = "../../../by-algorithm/lc0096/rust/lc0096_unique_binary_search_trees.rs"]
pub mod lc0096_unique_binary_search_trees;

#[path = "../../../by-algorithm/lc0102/rust/lc0102_binary_tree_level_order.rs"]
pub mod lc0102_binary_tree_level_order;

#[path = "../../../by-algorithm/lc0104/rust/lc0104_maximum_depth_of_binary_tree.rs"]
pub mod lc0104_maximum_depth_of_binary_tree;

#[path = "../../../by-algorithm/lc0127/rust/lc0127_word_ladder.rs"]
pub mod lc0127_word_ladder;

#[path = "../../../by-algorithm/lc0133/rust/lc0133_clone_graph.rs"]
pub mod lc0133_clone_graph;

#[path = "../../../by-algorithm/lc0136/rust/lc0136_single_number.rs"]
pub mod lc0136_single_number;

#[path = "../../../by-algorithm/lc0141/rust/lc0141_linked_list_cycle.rs"]
pub mod lc0141_linked_list_cycle;

#[path = "../../../by-algorithm/lc0142/rust/lc0142_linked_list_cycle_ii.rs"]
pub mod lc0142_linked_list_cycle_ii;

#[path = "../../../by-algorithm/lc0153/rust/lc0153_find_minimum_in_rotated_sorted_array.rs"]
pub mod lc0153_find_minimum_in_rotated_sorted_array;

#[path = "../../../by-algorithm/lc0155/rust/lc0155_min_stack.rs"]
pub mod lc0155_min_stack;

#[path = "../../../by-algorithm/lc0198/rust/lc0198_house_robber.rs"]
pub mod lc0198_house_robber;

#[path = "../../../by-algorithm/lc0200/rust/lc0200_number_of_islands.rs"]
pub mod lc0200_number_of_islands;

#[path = "../../../by-algorithm/lc0204/rust/lc0204_count_primes.rs"]
pub mod lc0204_count_primes;

#[path = "../../../by-algorithm/lc0206/rust/lc0206_reverse_linked_list.rs"]
pub mod lc0206_reverse_linked_list;

#[path = "../../../by-algorithm/lc0207/rust/lc0207_course_schedule.rs"]
pub mod lc0207_course_schedule;

#[path = "../../../by-algorithm/lc0209/rust/lc0209_minimum_size_subarray_sum.rs"]
pub mod lc0209_minimum_size_subarray_sum;

#[path = "../../../by-algorithm/lc0210/rust/lc0210_course_schedule_ii.rs"]
pub mod lc0210_course_schedule_ii;

#[path = "../../../by-algorithm/lc0214/rust/lc0214_shortest_palindrome.rs"]
pub mod lc0214_shortest_palindrome;

#[path = "../../../by-algorithm/lc0223/rust/lc0223_rectangle_area.rs"]
pub mod lc0223_rectangle_area;

#[path = "../../../by-algorithm/lc0226/rust/lc0226_invert_binary_tree.rs"]
pub mod lc0226_invert_binary_tree;

#[path = "../../../by-algorithm/lc0232/rust/lc0232_implement_queue_using_stacks.rs"]
pub mod lc0232_implement_queue_using_stacks;

#[path = "../../../by-algorithm/lc0236/rust/lc0236_lowest_common_ancestor.rs"]
pub mod lc0236_lowest_common_ancestor;

#[path = "../../../by-algorithm/lc0239/rust/lc0239_sliding_window_maximum.rs"]
pub mod lc0239_sliding_window_maximum;

#[path = "../../../by-algorithm/lc0300/rust/lc0300_longest_increasing_subsequence.rs"]
pub mod lc0300_longest_increasing_subsequence;

#[path = "../../../by-algorithm/lc0312/rust/lc0312_burst_balloons.rs"]
pub mod lc0312_burst_balloons;

#[path = "../../../by-algorithm/lc0370/rust/lc0370_range_addition.rs"]
pub mod lc0370_range_addition;

#[path = "../../../by-algorithm/lc0372/rust/lc0372_super_pow.rs"]
pub mod lc0372_super_pow;

#[path = "../../../by-algorithm/lc0384/rust/lc0384_shuffle_an_array.rs"]
pub mod lc0384_shuffle_an_array;

#[path = "../../../by-algorithm/lc0398/rust/lc0398_random_pick_index.rs"]
pub mod lc0398_random_pick_index;

#[path = "../../../by-algorithm/lc0416/rust/lc0416_partition_equal_subset_sum.rs"]
pub mod lc0416_partition_equal_subset_sum;

#[path = "../../../by-algorithm/lc0435/rust/lc0435_non_overlapping_intervals.rs"]
pub mod lc0435_non_overlapping_intervals;

#[path = "../../../by-algorithm/lc0455/rust/lc0455_assign_cookies.rs"]
pub mod lc0455_assign_cookies;

#[path = "../../../by-algorithm/lc0470/rust/lc0470_rand10_using_rand7.rs"]
pub mod lc0470_rand10_using_rand7;

#[path = "../../../by-algorithm/lc0516/rust/lc0516_longest_palindromic_subsequence.rs"]
pub mod lc0516_longest_palindromic_subsequence;

#[path = "../../../by-algorithm/lc0523/rust/lc0523_continuous_subarray_sum.rs"]
pub mod lc0523_continuous_subarray_sum;

#[path = "../../../by-algorithm/lc0560/rust/lc0560_subarray_sum_equals_k.rs"]
pub mod lc0560_subarray_sum_equals_k;

#[path = "../../../by-algorithm/lc0583/rust/lc0583_delete_operation_for_two_strings.rs"]
pub mod lc0583_delete_operation_for_two_strings;

#[path = "../../../by-algorithm/lc0587/rust/lc0587_erect_the_fence.rs"]
pub mod lc0587_erect_the_fence;

#[path = "../../../by-algorithm/lc0647/rust/lc0647_palindromic_substrings.rs"]
pub mod lc0647_palindromic_substrings;

#[path = "../../../by-algorithm/lc0704/rust/lc0704_binary_search.rs"]
pub mod lc0704_binary_search;

#[path = "../../../by-algorithm/lc0743/rust/lc0743_network_delay_time.rs"]
pub mod lc0743_network_delay_time;

#[path = "../../../by-algorithm/lc0787/rust/lc0787_cheapest_flights_within_k_stops.rs"]
pub mod lc0787_cheapest_flights_within_k_stops;

#[path = "../../../by-algorithm/lc0912/rust/lc0912_sort_an_array.rs"]
pub mod lc0912_sort_an_array;

#[path = "../../../by-algorithm/lc0994/rust/lc0994_rotting_oranges.rs"]
pub mod lc0994_rotting_oranges;

#[path = "../../../by-algorithm/lc1143/rust/lc1143_longest_common_subsequence.rs"]
pub mod lc1143_longest_common_subsequence;

#[path = "../../../by-algorithm/lc1584/rust/lc1584_min_cost_to_connect_all_points.rs"]
pub mod lc1584_min_cost_to_connect_all_points;

