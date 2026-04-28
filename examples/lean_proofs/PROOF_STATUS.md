---
title: Lean 形式化证明状态速查表
description: 所有项目自有 Lean 4 文件的证明完成度一览
version: 1.0
last_updated: 2026-04-29
---

# Lean 形式化证明状态速查表 / Lean Proof Status Quick Reference

> **适用范围**: `examples/lean_proofs/` 下的项目自有文件（不含 `mathlib/` 依赖存根）
> **审计日期**: 2026-04-29

---

## 图例 / Legend

| 标识 | 状态 | 含义 |
|------|------|------|
| 🟢 | **complete** | 无 `sorry`，完整证明 |
| 🟡 | **partial** | 部分定理已证，部分 `sorry` |
| 🔴 | **wip** | 仅规约框架，核心定理均为 `sorry` |

---

## 一、LeetCode 专题证明 / LeetCode Proofs

共 **14** 题，其中 🟢 1 题、🟡 6 题、🔴 7 题。

| 题号 | 文件 | 状态 | sorry 数 | 核心定理状态 |
|------|------|------|---------|-------------|
| LC 1 | `FormalAlgorithm/leetcode/lc0001_two_sum.lean` | 🟡 partial | 4 | `finds_solution` sorry, `result_correct` sorry, `terminates` sorry |
| LC 3 | `FormalAlgorithm/leetcode/lc0003_longest_substring.lean` | 🔴 wip | 8 | 核心定理均为 sorry |
| LC 15 | `FormalAlgorithm/leetcode/lc0015_3sum.lean` | 🔴 wip | 4 | 核心定理均为 sorry |
| LC 21 | `FormalAlgorithm/leetcode/lc0021_merge_two_sorted_lists.lean` | 🟡 partial | 5 | `preserves_sorted` sorry, `multiset_eq` ✅, `length` sorry, `terminates` sorry |
| LC 53 | `FormalAlgorithm/leetcode/lc0053_maximum_subarray.lean` | 🔴 wip | 4 | 核心定理均为 sorry |
| LC 70 | `FormalAlgorithm/leetcode/lc0070_climbing_stairs.lean` | 🟢 complete | 0 | 全部已证 ✅ |
| LC 72 | `FormalAlgorithm/leetcode/lc0072_edit_distance.lean` | 🟡 partial | 9 | `optimal_substructure` sorry, `nonneg` ✅, `zero_iff_eq` sorry, `symmetric` sorry, `triangle` sorry |
| LC 104 | `FormalAlgorithm/leetcode/lc0104_maximum_depth_of_binary_tree.lean` | 🟡 partial | 3 | `eq_longest_path` sorry, `le_nodeCount` ✅, `terminates` ✅ |
| LC 136 | `FormalAlgorithm/leetcode/lc0136_single_number.lean` | 🟡 partial | 8 | `xor_self` sorry, `xor_zero` sorry, `xor_comm` sorry, `xor_assoc` sorry, `correct` sorry, `group_axioms` ✅ |
| LC 141 | `FormalAlgorithm/leetcode/lc0141_linked_list_cycle.lean` | 🟡 partial | 4 | `cycle_implies_meet` sorry, `no_cycle_reaches_end` sorry, `correctness` sorry, `cycle_meet` ✅ |
| LC 198 | `FormalAlgorithm/leetcode/lc0198_house_robber.lean` | 🔴 wip | 3 | 核心定理均为 sorry |
| LC 200 | `FormalAlgorithm/leetcode/lc0200_number_of_islands.lean` | 🔴 wip | 6 | 核心定理均为 sorry |
| LC 207 | `FormalAlgorithm/leetcode/lc0207_course_schedule.lean` | 🔴 wip | 7 | 核心定理均为 sorry |
| LC 704 | `FormalAlgorithm/leetcode/lc0704_binary_search.lean` | 🔴 wip | 6 | 核心定理均为 sorry |

---

## 二、算法核心证明 / Core Algorithm Proofs

位于 `FormalAlgorithm/` 目录，共 **10** 个文件。

| 文件 | 状态 | sorry 数 | 备注 |
|------|------|---------|------|
| `FormalAlgorithm.lean` | 🟢 complete | 0 | 项目入口，无证明义务 |
| `FormalAlgorithm/BasicTypes.lean` | 🟢 complete | 0 | 基础类型定义 |
| `FormalAlgorithm/counting_sort.lean` | 🟡 partial | 3 | 有序性与计数守恒已证；排列性质 sorry |
| `FormalAlgorithm/dependent_types.lean` | 🟢 complete | 0 | 依赖类型示例 |
| `FormalAlgorithm/floyd_warshall.lean` | 🔴 wip | 3 | 核心正确性定理 sorry |
| `FormalAlgorithm/graph_proofs.lean` | 🔴 wip | 4 | BFS 可达性与完备性 sorry |
| `FormalAlgorithm/hott_basics.lean` | 🟢 complete | 0 | 同伦类型论基础 |
| `FormalAlgorithm/ListReverse.lean` | 🟢 complete | 0 | 列表反转证明 |
| `FormalAlgorithm/NatInduction.lean` | 🟢 complete | 0 | 自然数归纳法示例 |
| `FormalAlgorithm/simple_types.lean` | 🟢 complete | 0 | 简单类型示例 |
| `FormalAlgorithm/sorting_proofs.lean` | 🟢 complete | 0 | 排序证明基础 |

---

## 三、基础测试与练习文件 / Basic Tests & Exercises

位于 `examples/lean_proofs/` 根目录，共 **43** 个文件。

| 状态 | 数量 | 文件列表 |
|------|------|---------|
| 🟢 complete | 41 | `test_brute.lean`, `test_chain.lean`, `test_contra.lean`, `test_countfix.lean`, `test_ed.lean`, `test_exists_unique.lean`, `test_getq.lean`, `test_getq2.lean`, `test_happend.lean`, `test_happend2.lean`, `test_happend3.lean`, `test_length.lean`, `test_log.lean`, `test_max_eq.lean`, `test_max_le.lean`, `test_max_le_max.lean`, `test_mulmod.lean`, `test_omega2.lean`, `test_option.lean`, `test_option2.lean`, `test_optionsome.lean`, `test_optionsome2.lean`, `test_refine.lean`, `test_rfl.lean`, `test_rfl2.lean`, `test_simpall.lean`, `test_twosum.lean`, `test_twosum2.lean`, `test_twosum3.lean`, `test_use.lean`, `test_wf.lean`, `test_wf2.lean`, `test_wf3.lean`, `test_wf4.lean`, `test_wf5.lean`, `test_wf6.lean`, `test_wf7.lean`, `test_wf8.lean`, `test_xor.lean`, `test_xor2.lean` |
| 🔴 wip | 2 | `test_abs.lean` (1 sorry), `test_mod.lean` (1 sorry) |

---

## 四、统计摘要 / Summary

```text
总文件数          : 67
🟢 complete      : 49 (73.1%)
🟡 partial       :  7 (10.5%)
🔴 wip           : 11 (16.4%)

总 sorry 数       : 83
LeetCode 题数     : 14
LeetCode complete :  1 (lc0070)
```

---

## 五、如何贡献 / How to Contribute

1. **查看 🔴 wip 文件**：了解已建立的规约框架和证明思路注释。
2. **优先认领 🟡 partial 文件**：证明骨架已搭好，只需填充 `sorry` 处。
3. **参考 🟢 complete 文件**：如 `lc0070_climbing_stairs.lean`，学习完整的 Lean 4 证明风格。
4. **修改后更新状态**：完成证明后，将文件头部注释中的 `Status` 改为 `complete`，并更新 `Sorry Count` 为 `0`。

> 详细优先级与完成建议请参阅 [`docs/项目维护/Lean形式化证明状态审计报告_2026-04-29.md`](../../docs/项目维护/Lean形式化证明状态审计报告_2026-04-29.md)。
