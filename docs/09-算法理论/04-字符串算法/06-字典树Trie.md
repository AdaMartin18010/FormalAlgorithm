# 字典树（Trie / Prefix Tree）

## 概述

字典树（Trie）是一种树形数据结构，用于高效存储和检索字符串集合。它的核心优势在于：所有拥有共同前缀的字符串共享相同的路径，使得前缀查询的时间复杂度仅与模式长度相关。

## 结构定义

- **根节点**：空字符串
- **边**：标记为单个字符
- **路径**：从根到某节点的路径表示一个前缀
- **终止标记**：某些节点标记为"单词结束"

## 基本操作

### 插入

时间：$O(m)$，$m$ 为单词长度

```
node = root
for each char c in word:
    if node has no child c:
        create child c
    node = node.child[c]
node.is_end = true
```

### 搜索

时间：$O(m)$

```
node = root
for each char c in word:
    if node has no child c:
        return false
    node = node.child[c]
return node.is_end
```

### 前缀查询

时间：$O(m)$

返回是否存在以给定字符串为前缀的单词。

## 空间优化

| 变体 | 优化策略 | 空间 |
|------|---------|------|
| 标准 Trie | 每个节点固定大小字母表 | $O(n \cdot m \cdot |\Sigma|)$ |
| 压缩 Trie | 合并单分支节点 | $O(n)$ |
| 双数组 Trie | BASE/CHECK 数组压缩 | $O(n)$，常数极小 |
| 后缀树 | 存储所有后缀 | $O(n)$ |

## 经典应用

| 应用 | Trie 的作用 |
|------|------------|
| 自动补全 | 前缀遍历所有后代叶子 |
| 拼写检查 | 快速判断单词是否存在 |
| IP 路由（最长前缀匹配）| 二进制 Trie（Patricia Tree）|
| 字符串排序 | 按 Trie 中序遍历输出 |

## 与哈希表的对比

| 操作 | Trie | 哈希表 |
|------|------|--------|
| 精确查找 | $O(m)$ | $O(1)$ 平均 |
| 前缀查询 | $O(m)$ | ❌ 需遍历所有键 |
| 最长前缀匹配 | $O(m)$ | ❌ 不支持 |
| 按键排序输出 | $O(n)$ 中序 | ❌ 需额外排序 |
| 内存 | 较高 | 较低 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/data_structures.ts` → `Trie`
- Java: `examples/algorithms-java/`（可扩展）
- Rust: `examples/algorithms/src/trie.rs`
- Go: `examples/algorithms-go/`（可扩展）
