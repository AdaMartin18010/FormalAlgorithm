# ⚠️ 目录已迁移

本目录（\examples/algorithms/\）中的内容已完成迁移与整合：

## 迁移去向

| 原内容 | 目标位置 | 说明 |
|--------|---------|------|
| Rust 经典算法实现 | \examples/algorithms-rust/src/classic/\ | 按模块分类存放 |
| Rust LeetCode 实现 | \examples/algorithms-rust/src/leetcode/\ | 与 \lgorithms-rust/\ 原有实现合并 |
| Go 算法实现 | \examples/algorithms-go/\ | 已移动至 Go 专属目录 |
| Python 算法实现 | \examples/algorithms-python/\ | 已移动至 Python 专属目录 |
| Cargo 项目配置 | \examples/algorithms-rust/Cargo.toml\ | 合并入统一 Rust 项目 |
| 性能基准测试 | \examples/algorithms-rust/benches/\ | 合并入统一 Rust 项目 |

## 重复文件处理

以下 8 道 LeetCode 题目在 \lgorithms/\ 和 \lgorithms-rust/\ 中均有实现，已保留 \lgorithms-rust/\ 中更规范的版本，并删除 \lgorithms/\ 中的旧版本：

- LeetCode 11. Container With Most Water
- LeetCode 46. Permutations
- LeetCode 55. Jump Game
- LeetCode 70. Climbing Stairs
- LeetCode 127. Word Ladder
- LeetCode 136. Single Number
- LeetCode 236. Lowest Common Ancestor
- LeetCode 994. Rotting Oranges

## 后续规范

所有多语言实现请遵循：
- [多语言实现规范手册](../../docs/项目维护/多语言实现规范手册.md)
- [跨语言对照索引](../CROSS_LANGUAGE_INDEX.md)

> 本目录保留为占位符，以便历史链接平滑过渡。后续将视情况完全移除。
