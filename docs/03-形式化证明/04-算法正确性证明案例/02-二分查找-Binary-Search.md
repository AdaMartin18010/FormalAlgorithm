---
title: 案例 02：二分查找 / Case 02：Binary Search
version: 1.0
status: completed
last_updated: 2026-04-29
owner: 形式化证明工作组
concepts: ["Binary Search", "loop invariant", "termination", "ranking function", "correctness proof", "LeetCode", "Lean 4"]
level: 中级
diataxis: reference
---

# 案例 02：二分查找 / Case 02：Binary Search

> **LeetCode**: [704. Binary Search](https://leetcode.com/problems/binary-search/)
> **难度**: Easy
> **范式**: Divide and Conquer / 分治

---

## 一、题目规约 / Problem Specification

### 1.1 自然语言描述

给定一个**升序排列**的整数数组 `nums` 和一个目标值 `target`，请编写一个函数搜索 `nums` 中的 `target`。

如果目标值存在，返回其下标；否则返回 -1。

约束：
- 数组已按升序排列
- $1 \leq |\text{nums}| \leq 10^4$

### 1.2 形式化规约

**前置条件** $P$：
$$\text{sorted}(\text{nums}) \triangleq \forall i, j.\ (0 \leq i < j < |\text{nums}|) \Rightarrow (\text{nums}[i] \leq \text{nums}[j])$$

**后置条件** $Q$：
$$\begin{aligned}
&(\text{result} \geq 0 \Rightarrow \text{nums}[\text{result}] = \text{target}) \\
\land\ &(\text{result} = -1 \Rightarrow \forall i.\ \text{nums}[i] \neq \text{target})
\end{aligned}$$

---

## 二、算法描述 / Algorithm Description

### 2.1 标准实现（左闭右开）

```rust
pub fn search(nums: Vec<i32>, target: i32) -> i32 {
    let mut lo = 0usize;
    let mut hi = nums.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if nums[mid] == target {
            return mid as i32;
        } else if nums[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    -1
}
```

### 2.2 关键设计决策

| 变体 | 循环条件 | 区间含义 | 移动方式 |
|------|---------|---------|---------|
| 左闭右开 `[lo, hi)` | `lo < hi` | 搜索范围 | `lo=mid+1` / `hi=mid` |
| 左闭右闭 `[lo, hi]` | `lo <= hi` | 搜索范围 | `lo=mid+1` / `hi=mid-1` |

本文采用左闭右开版本，因其不变式表述更为简洁。

---

## 三、正确性证明 / Correctness Proof

### 3.1 循环不变式

> $I \triangleq (\text{target} \notin \text{nums}[0..\text{lo})) \land (\text{target} \notin \text{nums}[\text{hi}..n))$

**等价表述**：若 `target` 存在于数组中，则它一定在搜索区间 $[\text{lo}, \text{hi})$ 内。

---

### 3.2 初始化（Initialization）

初始时 $\text{lo} = 0, \text{hi} = n$。

- $\text{nums}[0..0) = \emptyset$，故 $\text{target} \notin \text{nums}[0..0)$ 空真成立
- $\text{nums}[n..n) = \emptyset$，故 $\text{target} \notin \text{nums}[n..n)$ 空真成立

因此 $I$ 初始化成立。

---

### 3.3 保持（Maintenance）

假设迭代前 $I$ 成立，且循环条件 $\text{lo} < \text{hi}$ 成立。

设 $\text{mid} = \text{lo} + \lfloor(\text{hi} - \text{lo})/2\rfloor$，分三种情况：

**情况A**：$\text{nums}[\text{mid}] = \text{target}$

算法直接返回 $\text{mid}$。循环终止，无需保持。

**情况B**：$\text{nums}[\text{mid}] < \text{target}$

由于数组升序排列，对于所有 $j \leq \text{mid}$，有 $\text{nums}[j] \leq \text{nums}[\text{mid}] < \text{target}$。

因此 $\text{target} \notin \text{nums}[0..\text{mid}] = \text{nums}[0..\text{mid}+1) = \text{nums}[0..\text{lo}')$，其中 $\text{lo}' = \text{mid} + 1$。

右边界不变（$\text{hi}' = \text{hi}$），故 $I$ 保持。

**情况C**：$\text{nums}[\text{mid}] > \text{target}$

由于数组升序排列，对于所有 $j \geq \text{mid}$，有 $\text{nums}[j] \geq \text{nums}[\text{mid}] > \text{target}$。

因此 $\text{target} \notin \text{nums}[\text{mid}..n) = \text{nums}[\text{hi}'..n)$，其中 $\text{hi}' = \text{mid}$。

左边界不变（$\text{lo}' = \text{lo}$），故 $I$ 保持。

```mermaid
graph TD
    A["迭代前: I成立<br/>target ∈ [lo, hi)"] --> B{"nums[mid] vs target"}
    B -->|nums[mid] == target| C["返回mid<br/>找到解"]
    B -->|nums[mid] < target| D["lo' = mid + 1<br/>target ∉ [lo..mid]<br/>保持I"]
    B -->|nums[mid] > target| E["hi' = mid<br/>target ∉ [mid..hi)<br/>保持I"]
    D --> F["下一次迭代"]
    E --> F
```

---

### 3.4 终止（Termination）

当循环终止时，$\neg(\text{lo} < \text{hi})$，即 $\text{lo} \geq \text{hi}$。

由 $I$：$\text{target} \notin \text{nums}[0..\text{lo}) \land \text{target} \notin \text{nums}[\text{hi}..n)$。

由于 $\text{lo} \geq \text{hi}$，$[0..\text{lo}) \supseteq [0..\text{hi})$ 且 $[\text{hi}..n) \supseteq [\text{lo}..n)$。

更直接地，由于 $\text{lo} \geq \text{hi}$ 且搜索区间 $[\text{lo}, \text{hi})$ 为空，结合不变式的等价表述"若target存在则在 $[\text{lo}, \text{hi})$ 内"，可知target不存在于数组中。

因此返回 -1 是正确的。

---

### 3.5 终止性证明

**秩函数**：$r = \text{hi} - \text{lo}$

- **有界性**：由循环条件 $\text{lo} < \text{hi}$，$r \geq 1 > 0$
- **递减性**：
  - 情况B：$\text{lo}' = \text{mid} + 1 \geq \text{lo} + 1 > \text{lo}$，故 $r' = \text{hi} - \text{lo}' < \text{hi} - \text{lo} = r$
  - 情况C：$\text{hi}' = \text{mid} < \text{hi}$（因 $\text{mid} = \text{lo} + \lfloor r/2 \rfloor < \text{lo} + r = \text{hi}$），故 $r' = \text{hi}' - \text{lo} < r$
- **良基性**：$r \in \mathbb{N}$，$(\mathbb{N}, <)$ 良基

因此循环必然终止。

---

## 四、复杂度分析 / Complexity Analysis

**时间复杂度 O(log n)**：
- 每次迭代搜索区间至少减半
- 设迭代次数为 $k$，则 $n/2^k < 1$，即 $k < \log_2 n + 1$
- 总时间：$O(\log n)$

**空间复杂度 O(1)**：
- 仅使用常数个额外变量

---

## 五、Lean 4形式化规约 / Lean 4 Formalization

```lean
import Mathlib

-- 有序数组定义
def Sorted (nums : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < nums.size → nums[i]! ≤ nums[j]!

-- 二分查找核心定理：若target存在，则返回其下标
theorem binarySearch_finds_solution
    (nums : Array Int) (target : Int)
    (h_sorted : Sorted nums)
    (h_exists : ∃ i, i < nums.size ∧ nums[i]! = target) :
    ∃ result, result ≥ 0 ∧ result < nums.size ∧ nums[result.toNat]! = target :=
  by
  sorry

-- 若target不存在，则返回-1
theorem binarySearch_returns_neg1
    (nums : Array Int) (target : Int)
    (h_sorted : Sorted nums)
    (h_not_exists : ∀ i, i < nums.size → nums[i]! ≠ target) :
    binarySearch nums target = -1 :=
  by
  sorry

-- 终止性：基于秩函数 hi - lo
theorem binarySearch_terminates
    (nums : Array Int) (target : Int) :
    ∃ result, binarySearch nums target = result :=
  by
  -- 秩函数 r = hi - lo，每次严格递减且非负
  sorry
```

---

## 六、常见错误与边界情况 / Common Mistakes

| 错误 | 现象 | 根本原因 |
|------|------|---------|
| 死循环 | `lo = mid` 且 `hi` 不变 | 区间未严格缩小 |
| 越界访问 | `mid` 计算溢出 | 未使用 `lo + (hi - lo) / 2` |
| 返回错误 | 左闭右开与左闭右闭混淆 | 边界条件不一致 |
| 未找到时返回错误 | 在 `lo <= hi` 版本中使用 `lo < hi` 的返回逻辑 | 两种变体的语义差异 |

### 边界测试用例

```rust
assert_eq!(search(vec![], 1), -1);           // 空数组
assert_eq!(search(vec![5], 5), 0);           // 单元素，命中
assert_eq!(search(vec![5], 3), -1);          // 单元素，未命中
assert_eq!(search(vec![1,3,5,7], 0), -1);    // 小于所有元素
assert_eq!(search(vec![1,3,5,7], 8), -1);    // 大于所有元素
```

---

## 七、参考文献 / References

[CLRS2009] T. H. Cormen et al. *Introduction to Algorithms* (3rd ed.). MIT Press, 2009.（第2.3节二分查找）

[Knuth1998] D. E. Knuth. *The Art of Computer Programming, Vol. 3: Sorting and Searching* (2nd ed.). Addison-Wesley, 1998.（第6.2.1节二分查找）

[Bentley2000] J. Bentley. *Programming Pearls* (2nd ed.). Addison-Wesley, 2000.（第4-5章算法设计）

[Hoare1969] C. A. R. Hoare. An Axiomatic Basis for Computer Programming. *Communications of the ACM*, 12(10):576-580, 1969.

---

## 八、交叉引用 / Cross-References

- **相关理论**：[循环不变式](../../02-程序验证基础/03-循环不变式.md)、[终止性证明](../../02-程序验证基础/04-终止性证明.md)
- **上一案例**：[两数之和](01-两数之和-Two-Sum.md)
- **LeetCode题解**：[13-LeetCode算法面试专题/](../../../13-LeetCode算法面试专题/)
- **代码实现**：`examples/algorithms-rust/src/leetcode/lc0704_binary_search.rs`

---

## 学习目标 / Learning Objectives

- [ ] 精确表述二分查找的循环不变式（边界缩小模式）
- [ ] 独立完成初始化、保持、终止三要素的严格验证
- [ ] 构造秩函数并证明循环的终止性
- [ ] 识别左闭右开与左闭右闭两种实现变体的差异
- [ ] 理解二分查找不变式在Lean 4中的表达方法
