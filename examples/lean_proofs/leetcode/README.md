# LeetCode 算法形式化证明 — Lean 4

## 目录定位

本目录存放 LeetCode 经典算法正确性的 Lean 4 形式化证明，作为 `docs/03-形式化证明/` 与 `docs/13-LeetCode算法面试专题/` 的严格数学基础。每个文件对应一道 LeetCode 题目，证明其算法实现的**部分正确性**与**终止性**。

## 文件命名规范

```
lc{题号}_{题目简称}.lean
```

示例：

- `lc0704_binary_search.lean` — 二分查找正确性证明

## 内容规范模板

每个 `.lean` 文件至少包含以下内容：

1. **问题实例的形式化定义**
   - 输入约束的谓词（如 `IsSorted`、`IsRotatedSorted`）
   - 目标值存在性的定义

2. **算法的 Lean 实现**
   - 使用 `def` 给出可执行的算法函数
   - 或仅给出规范描述（specification）

3. **循环不变式的形式化陈述**
   - 使用 `def Invariant (nums : Array Int) (target : Int) (left right : Nat) : Prop := ...`

4. **核心定理**
   - **存在性定理**：若目标在数组中，则算法返回其索引
   - **否定性定理**：若目标不在数组中，则算法返回 -1
   - **终止性定理**：算法必在有限步内终止

5. **证明骨架**
   - 即使不能完成全部证明，也要写出完整的定理陈述
   - 未证部分使用 `sorry` 标记，并附 `TODO` 说明

```lean
/-
  lc0704_binary_search.lean
  LeetCode 704. 二分查找正确性的形式化证明（Lean 4）

  证明目标：
    1. 若 target 在有序数组 nums 中，search 返回其索引。
    2. 若 target 不在 nums 中，search 返回 -1。
    3. 算法必终止。

  依赖: Mathlib4 的序理论和自然数工具
-/]

-- 1. 问题定义

def IsSorted (nums : Array Int) : Prop := ...

def IsInRange (nums : Array Int) (target : Int) : Prop := ...

-- 2. 算法实现（规范描述）

def binarySearch (nums : Array Int) (target : Int) : Int := ...

-- 3. 循环不变式
def LoopInvariant (nums : Array Int) (target : Int) (left right : Nat) : Prop := ...

-- 4. 核心定理

theorem binary_search_found
    (nums : Array Int) (target : Int)
    (h_sorted : IsSorted nums)
    (h_exists : ∃ i, nums[i]! = target)
    : ∃ i, binarySearch nums target = i ∧ nums[i]! = target := by
  sorry -- TODO: 使用循环不变式归纳证明

theorem binary_search_not_found
    (nums : Array Int) (target : Int)
    (h_sorted : IsSorted nums)
    (h_not_exists : ∀ i, nums[i]! ≠ target)
    : binarySearch nums target = -1 := by
  sorry -- TODO: 证明区间为空时 target 不存在

theorem binary_search_terminates
    (nums : Array Int) (target : Int)
    : WellFoundedRelation ... := by
  sorry -- TODO: 以区间长度作为 well-founded 度量
```

## 与 docs/ 的交叉引用

- 算法面试专题：`docs/13-LeetCode算法面试专题/02-算法范式专题/`
- 形式化证明基础：`docs/03-形式化证明/`
- 逻辑系统：`docs/06-逻辑系统/`
- 类型理论：`docs/05-类型理论/`

在文件头部的模块注释中使用相对路径引用，例如：

```lean
/-
  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/
```

## 依赖管理

- 统一使用 `lakefile.toml` 中声明的 `mathlib4` 版本
- 优先使用 Mathlib4 的 `Order`、`Nat`、`Array` 工具
- 避免引入与项目现有依赖冲突的外部包
