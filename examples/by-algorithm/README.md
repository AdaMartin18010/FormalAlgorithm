# 算法实现示例（按算法组织）/ Algorithm Implementations (By Algorithm)

> **组织模式**: Rosetta Code 模式 — 每个算法一个目录，内含各语言子目录

## 目录结构

```
examples/by-algorithm/
├── lc0001/          # LeetCode 1. Two Sum
│   ├── rust/
│   ├── python/
│   ├── go/
│   └── ...
├── lc0003/          # LeetCode 3. Longest Substring Without Repeating Characters
│   └── ...
├── lc0704/          # LeetCode 704. Binary Search
│   └── ...
└── classic/         # 经典算法（非LeetCode）
    ├── binary-search/
    ├── quicksort/
    └── ...
```

## 使用方式

### 按算法浏览（推荐学习者）

```bash
# 查看 Two Sum 的所有语言实现
cd examples/by-algorithm/lc0001
ls
```

### 按语言浏览（推荐开发者）

```bash
# 查看 Rust 的所有 LeetCode 实现
cd examples/algorithms-rust/src/leetcode
```

## 语言覆盖

| 语言 | 目录 | 状态 |
|------|------|------|
| Rust | `by-algorithm/*/rust/` | 最完整 |
| Python | `by-algorithm/*/python/` | 较完整 |
| Go | `by-algorithm/*/go/` | 较完整 |
| TypeScript | `by-algorithm/*/typescript/` | 基础 |
| Java | `by-algorithm/*/java/` | 基础 |
| C++ | `by-algorithm/*/cpp/` | 基础 |
| C | `by-algorithm/*/c/` | 基础 |
| JavaScript | `by-algorithm/*/js/` | 基础 |

## 与 docs/13-LeetCode 的关联

每个 `lc{题号}/` 目录对应 [docs/13-LeetCode算法面试专题](../../docs/13-LeetCode算法面试专题/) 中的题解文档。
