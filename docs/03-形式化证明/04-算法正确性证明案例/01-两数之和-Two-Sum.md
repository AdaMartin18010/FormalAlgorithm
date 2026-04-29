---
title: 案例 01：两数之和 / Case 01：Two Sum
version: 1.0
status: completed
last_updated: 2026-04-29
owner: 形式化证明工作组
concepts: ["Two Sum", "hash table", "loop invariant", "correctness proof", "LeetCode", "Lean 4"]
level: 入门
diataxis: reference
---

# 案例 01：两数之和 / Case 01：Two Sum

> **LeetCode**: [1. Two Sum](https://leetcode.com/problems/two-sum/)
> **难度**: Easy
> **范式**: Hash Table / 哈希表

---

## 一、题目规约 / Problem Specification

### 1.1 自然语言描述

给定一个整数数组 `nums` 和一个整数目标值 `target`，请你在该数组中找出**和为目标值**的两个整数，并返回它们的数组下标。

约束：
- 每种输入只会对应一个答案
- 同一个元素不能使用两遍
- 答案可以按任意顺序返回

### 1.2 形式化规约

**前置条件** $P$：
$$\text{nums} \in \text{Array}(\mathbb{Z}) \land 2 \leq |\text{nums}| \leq 10^4 \land \text{target} \in \mathbb{Z}$$

**后置条件** $Q$：
$$\exists i, j.\ (0 \leq i < j < |\text{nums}|) \land (\text{nums}[i] + \text{nums}[j] = \text{target})$$

**唯一性约束**：
$$\forall i_1, j_1, i_2, j_2.\ (\text{nums}[i_1] + \text{nums}[j_1] = \text{target} \land \text{nums}[i_2] + \text{nums}[j_2] = \text{target}) \Rightarrow \{i_1, j_1\} = \{i_2, j_2\}$$

---

## 二、算法描述 / Algorithm Description

### 2.1 暴力解法 O(n²)

枚举所有 $(i, j)$ 对，检查是否满足 $\text{nums}[i] + \text{nums}[j] = \text{target}$。

### 2.2 哈希表解法 O(n)（最优解）

遍历数组一次，用哈希表记录每个值对应的下标。对于当前元素 $\text{nums}[i]$，检查 $\text{target} - \text{nums}[i]$ 是否在哈希表中。

```rust
use std::collections::HashMap;

pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
    let mut map: HashMap<i32, usize> = HashMap::new();
    for (i, &num) in nums.iter().enumerate() {
        let complement = target - num;
        if let Some(&j) = map.get(&complement) {
            return vec![j as i32, i as i32];
        }
        map.insert(num, i);
    }
    vec![]  // 根据题意，此行不会执行
}
```

---

## 三、正确性证明 / Correctness Proof

我们以**哈希表解法**为对象进行严格证明。

### 3.1 循环不变式

> $I(i) \triangleq \forall j < i.\ \text{map}[\text{nums}[j]] = j \land \forall j < k < i.\ \text{nums}[j] + \text{nums}[k] \neq \text{target}$

**文字表述**：
1. 哈希表中准确记录了所有已遍历元素的下标映射
2. 在已遍历的前缀 $[0, i)$ 中，不存在任何一对元素的和等于target

### 3.2 初始化（Initialization）

当 $i = 0$ 时，已遍历范围为空。性质1（空真）和性质2（空真）均平凡成立。

### 3.3 保持（Maintenance）

假设第 $i$ 次迭代前 $I(i)$ 成立。

**步骤1**：计算 $\text{complement} = \text{target} - \text{nums}[i]$。

**步骤2**：检查 $\text{complement}$ 是否在 $\text{map}$ 中。

- **情况A**：存在 $j < i$ 使得 $\text{map}[\text{complement}] = j$。
  这意味着 $\text{nums}[j] = \text{complement}$，即 $\text{nums}[j] + \text{nums}[i] = \text{target}$。
  算法返回 $[j, i]$，循环终止，找到了正确解。

- **情况B**：不存在这样的 $j$。
  这意味着对于所有 $j < i$，$\text{nums}[j] \neq \text{complement}$，即 $\text{nums}[j] + \text{nums}[i] \neq \text{target}$。
  执行 $\text{map}.\text{insert}(\text{nums}[i], i)$ 后：
  - 性质1仍然成立（新增了当前元素的准确映射）
  - 性质2扩展为 $[0, i+1)$，由 $I(i)$ 的假设和情况B的分析，新范围中仍无和为target的对

因此 $I(i+1)$ 成立。

### 3.4 终止（Termination）

若循环正常结束（未提前返回），则 $I(n)$ 成立，其中 $n = |\text{nums}|$。

由 $I(n)$ 的性质2：$\forall j < k < n.\ \text{nums}[j] + \text{nums}[k] \neq \text{target}$。

这与题目的存在性保证矛盾（题目保证有且仅有一个解）。因此根据题意，循环必然会在找到解时提前返回。

### 3.5 完备性与可靠性

- **完备性（Completeness）**：若解存在，算法一定会找到它。
  证明：设解为 $(j^*, i^*)$ 且 $j^* < i^*$。当迭代到 $i = i^*$ 时，$j^* < i^*$ 已在map中，故情况A触发，返回解。

- **可靠性（Soundness）**：算法返回的结果一定是正确解。
  证明：算法仅在情况A时返回，此时 $\text{nums}[j] + \text{nums}[i] = \text{target}$ 且 $j < i$。

---

## 四、复杂度分析 / Complexity Analysis

**时间复杂度 O(n)**：
- 单次遍历数组，每次哈希表操作平均 O(1)
- 总时间：$n$ 次迭代 $\times$ O(1) = O(n)

**空间复杂度 O(n)**：
- 最坏情况下哈希表存储 $n-1$ 个元素
- 总空间：O(n)

**严格推导**：
设 $T(n)$ 为输入规模为 $n$ 时的运行时间。
$$T(n) = \sum_{i=0}^{n-1} O(1) = O(n)$$

---

## 五、Lean 4形式化规约 / Lean 4 Formalization

```lean
import Mathlib

-- 问题类型定义
def TwoSumProblem (nums : Array Int) (target : Int) : Prop :=
  ∃ i j : Nat,
    i < nums.size ∧ j < nums.size ∧
    i ≠ j ∧ nums[i]! + nums[j]! = target

-- 哈希表解法的核心定理
theorem twoSumHash_finds_solution
    (nums : Array Int) (target : Int)
    (h_exists : TwoSumProblem nums target) :
    ∃ i j, i < nums.size ∧ j < nums.size ∧ i ≠ j ∧ nums[i]! + nums[j]! = target :=
  by
  -- 证明思路：遍历过程中维护不变式
  -- 若提前返回，则找到解；若遍历完未返回，与存在性假设矛盾
  sorry  -- 完整证明需要实现哈希表遍历的归纳论证

-- 结果正确性：返回的下标对应和为target
theorem twoSumHash_result_correct
    (nums : Array Int) (target : Int)
    (result : Array Nat)
    (h_result : result = twoSum nums target) :
    result.size = 2 ∧
    result[0]! < nums.size ∧ result[1]! < nums.size ∧
    result[0]! ≠ result[1]! ∧
    nums[result[0]!]! + nums[result[1]!]! = target :=
  by
  sorry

-- 终止性：算法必然在有限步内结束
theorem twoSumHash_terminates
    (nums : Array Int) (target : Int) :
    ∃ result, twoSum nums target = result :=
  by
  -- 秩函数：r(i) = nums.size - i
  -- 每次迭代i增加1，r严格递减，最多nums.size步后终止
  sorry
```

---

## 六、常见错误与边界情况 / Common Mistakes

| 错误 | 原因 | 正确做法 |
|------|------|---------|
| 同一元素使用两遍 | 先插入当前元素再检查 | 先检查补数，再插入当前元素 |
| 返回顺序错误 | 未注意题目要求的索引顺序 | 确保返回 `[较小索引, 较大索引]` |
| 哈希表冲突处理 | 相同值出现多次 | 题目保证唯一解，但实现时应注意覆盖问题 |
| 未处理无解情况 | 题目假设有解 | 实际工程中应返回 `Option` 类型 |

---

## 七、参考文献 / References

[CLRS2009] T. H. Cormen et al. *Introduction to Algorithms* (3rd ed.). MIT Press, 2009.（第11章哈希表）

[Hoare1969] C. A. R. Hoare. An Axiomatic Basis for Computer Programming. *Communications of the ACM*, 12(10):576-580, 1969.

[Dijkstra1976] E. W. Dijkstra. *A Discipline of Programming*. Prentice-Hall, 1976.

---

## 八、交叉引用 / Cross-References

- **相关理论**：[循环不变式](../../02-程序验证基础/03-循环不变式.md)
- **后续案例**：[二分查找](02-二分查找-Binary-Search.md)
- **LeetCode题解**：[13-LeetCode算法面试专题/01-数组与字符串/lc0001-two-sum](../../../13-LeetCode算法面试专题/)
- **代码实现**：`examples/algorithms-rust/src/leetcode/lc0001_two_sum.rs`

---

## 学习目标 / Learning Objectives

- [ ] 理解Two Sum问题的形式化规约
- [ ] 掌握哈希表解法的循环不变式构造与验证
- [ ] 能够独立完成完备性与可靠性证明
- [ ] 理解该案例与循环不变式通用理论的对应关系
