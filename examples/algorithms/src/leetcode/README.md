# LeetCode 算法实现 — Rust

## 目录定位

本目录存放 LeetCode 经典题目的工程级 Rust 实现，对标 `docs/13-LeetCode算法面试专题/` 的形式化分析与证明。所有实现遵循 LeetCode 官方函数签名，可直接用于刷题或面试准备。

## 文件命名规范

```
lc{题号}_{题目简称}.rs
```

示例：

- `lc0704_binary_search.rs` — 二分查找
- `lc0033_search_in_rotated_sorted_array.rs` — 搜索旋转排序数组
- `lc0153_find_minimum_in_rotated_sorted_array.rs` — 寻找旋转排序数组最小值

## 注释规范模板

每个公共函数必须包含以下 `///` docstring 区块：

```rust
/// {一句话功能描述}
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 已按升序排列，且所有元素互不相同（或按题意说明）
/// - **后置条件 (Post)**：若 `target ∈ nums`，返回唯一索引 `i` 使得 `nums[i] == target`；否则返回 `-1`
///
/// # 循环不变式
///
/// 设当前搜索区间为 `[left, right]`：
/// - 若 `target` 在 `nums` 中，则 `target` 的索引必在 `[left, right]` 内。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n) — 每次迭代将搜索区间减半
/// - **空间复杂度**：O(1) — 仅使用常数个额外变量
///
/// # 证明要点
///
/// - 正确性证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md`
/// - 终止性由区间严格递减保证
pub fn search(nums: Vec<i32>, target: i32) -> i32 { ... }
```

## 测试规范

每个文件必须包含 `#[cfg(test)] mod tests`：

1. **LeetCode 官方示例用例**：至少覆盖题目给出的所有示例
2. **边界条件**：
   - 空数组
   - 单元素数组
   - 全部相同元素（若适用）
   - 最大值/最小值元素
3. **稳定性与正确性**：与已知正确结果对比

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() { ... }

    #[test]
    fn test_empty() { ... }

    #[test]
    fn test_single_element() { ... }
}
```

## 与 docs/ 的交叉引用

- 算法范式分析：`docs/13-LeetCode算法面试专题/02-算法范式专题/`
- 数据结构专题：`docs/13-LeetCode算法面试专题/01-数据结构专题/`
- 形式化证明：`docs/03-形式化证明/`
- 复杂度理论：`docs/04-算法复杂度/`

在 docstring 中使用相对路径引用对应的文档，例如：

```
/// 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
```

## 代码风格

- 所有代码必须通过 `rustfmt` 格式化
- 使用 `cargo clippy` 检查无警告
- 优先使用迭代实现以降低栈空间消耗
