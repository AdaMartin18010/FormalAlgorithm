#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
清理公共示例库中的重复代码示例
"""

import re
from pathlib import Path

replacements = []

# Helper to add reference note
ref_note = (
    "> 💻 **代码示例引用**：完整实现可参见 "
    "[`examples/algorithms/src/`](../../../examples/algorithms/src/) 目录，"
    "或 [`docs/示例库/01-标准示例集.md`](../../示例库/01-标准示例集.md)。\n\n"
)

# ========== 1. 08-实现示例/01-Rust实现.md 中的排序代码块 ==========
path = Path("docs/08-实现示例/01-Rust实现.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 查找 pub struct QuickSort / pub struct MergeSort / pub struct HeapSort 等代码块
    # 这些代码块通常很长，包含完整实现
    old_pattern = r"(### \d+\.\d+ 排序算法实现 / Sorting Algorithm Implementations\n\n)"
    if "💻 **代码示例引用**" not in content and re.search(old_pattern, content):
        # 找到第一个排序代码块的位置，在其前面添加引用注释
        marker = "### 5.2 排序算法实现 / Sorting Algorithm Implementations\n\n"
        if marker in content:
            content = content.replace(
                marker,
                marker + ref_note,
            )
            path.write_text(content, encoding="utf-8")
            replacements.append((str(path), "排序算法实现引用"))

# ========== 2. 08-实现示例/03-Lean实现.md 中的HoTT示例 ==========
path = Path("docs/08-实现示例/03-Lean实现.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 查找 Circle / Sphere 定义
    if "Sphere" in content or "Circle" in content:
        marker = "### 3.3 同伦类型论示例 / Homotopy Type Theory Examples\n\n"
        if marker in content and "💻 **代码示例引用**" not in content:
            note = (
                "> 💻 **代码示例引用**：HoTT 圆/球面定义及高级形式化示例可参见 "
                "[`docs/05-类型理论/03-同伦类型论.md`](../../05-类型理论/03-同伦类型论.md)。\n\n"
            )
            content = content.replace(marker, marker + note)
            path.write_text(content, encoding="utf-8")
            replacements.append((str(path), "HoTT示例引用"))

# ========== 3. 07-计算模型/05-量子计算模型.md 中的量子门实现 ==========
path = Path("docs/07-计算模型/05-量子计算模型.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 查找实现示例章节
    marker = "## 8. 实现示例 (Implementation Examples)\n\n"
    if marker in content and "💻 **代码示例引用**" not in content:
        note = (
            "> 💻 **代码示例引用**：量子门实现的完整代码可参见 "
            "[`examples/`](../../examples/) 目录下的量子计算相关实现。\n\n"
        )
        content = content.replace(marker, marker + note)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "量子门实现引用"))

# ========== 4. 09-算法理论/01-算法基础/05-图算法理论.md 中的BFS/DFS实现 ==========
path = Path("docs/09-算法理论/01-算法基础/05-图算法理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 文件中有多个Rust代码块实现Graph/BFS/DFS/Dijkstra等
    # 在第一个Rust实现代码块前添加引用
    marker = "```rust\nuse std::collections::HashMap;\n"
    if marker in content and "💻 **代码示例引用**" not in content:
        # 找到第一个包含 "impl Graph" 的Rust代码块
        idx = content.find(marker)
        if idx != -1:
            # 找到该代码块前面的段落标题
            before = content[:idx].rstrip()
            line_start = before.rfind("\n") + 1
            heading = before[line_start:]
            if heading.startswith("###"):
                note = (
                    "> 💻 **代码示例引用**：图遍历算法（BFS/DFS）及图算法的完整实现可参见 "
                    "[`examples/algorithms/src/graph_bfs_dfs.rs`](../../../examples/algorithms/src/graph_bfs_dfs.rs) "
                    "及 [`docs/示例库/01-标准示例集.md`](../../示例库/01-标准示例集.md)。\n\n"
                )
                content = content[:idx] + "\n" + note + content[idx:]
                path.write_text(content, encoding="utf-8")
                replacements.append((str(path), "图遍历算法引用"))

# ========== 5. 09-算法理论/01-算法基础/06-动态规划理论.md 中的背包问题 ==========
path = Path("docs/09-算法理论/01-算法基础/06-动态规划理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    marker = "```rust\nuse std::cmp::max;\n"
    if marker in content and "💻 **代码示例引用**" not in content:
        idx = content.find(marker)
        if idx != -1:
            note = (
                "> 💻 **代码示例引用**：动态规划（包括0/1背包问题）的完整实现可参见 "
                "[`docs/示例库/01-标准示例集.md`](../../示例库/01-标准示例集.md) "
                "及 [`examples/`](../../../examples/) 目录。\n\n"
            )
            content = content[:idx] + "\n" + note + content[idx:]
            path.write_text(content, encoding="utf-8")
            replacements.append((str(path), "动态规划示例引用"))

# ========== 6. 04-算法复杂度/03-渐进分析.md 中的排序分析 ==========
path = Path("docs/04-算法复杂度/03-渐进分析.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 查找是否包含完整排序代码
    if "merge_sort" in content.lower() and "💻 **代码示例引用**" not in content:
        # 在文档开头引用块后添加说明
        marker = "### 3.4 动态规划分析 (Dynamic Programming Analysis)\n\n"
        if marker in content:
            note = (
                "> 💻 **代码示例引用**：排序算法与动态规划的实现示例及复杂度分析可参见 "
                "[`docs/示例库/01-标准示例集.md`](../../示例库/01-标准示例集.md)。\n\n"
            )
            content = content.replace(marker, marker + note)
            path.write_text(content, encoding="utf-8")
            replacements.append((str(path), "排序分析示例引用"))

print("=== 示例去重完成 ===")
for p, desc in replacements:
    print(f"[DONE] {p} -> {desc}")
print(f"\n共处理 {len(replacements)} 处重复示例")
