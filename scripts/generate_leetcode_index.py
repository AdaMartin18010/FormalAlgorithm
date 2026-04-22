#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成 LeetCode 全局索引和元数据文件（精确版）
"""

import os
import re
import csv
from pathlib import Path
from collections import defaultdict, Counter

ROOT = Path("e:/_src/FormalAlgorithm")
DOCS_DIR = ROOT / "docs/13-LeetCode算法面试专题"
EXAMPLES_DIR = ROOT / "examples"
APPENDIX_FILE = DOCS_DIR / "99-附录/01-LeetCode题号全局索引.md"
README_FILE = DOCS_DIR / "README.md"
PROJECT_STRUCTURE = ROOT / "PROJECT_STRUCTURE.md"
CSV_FILE = ROOT / "scripts/leetcode_index.csv"

def extract_problem_number_from_filename(filename):
    """从文件名提取题号，支持 lc0001, lc1234, 剑指Offer_XX 等格式"""
    m = re.search(r'lc0*(\d+)', filename, re.IGNORECASE)
    if m:
        return int(m.group(1))
    m = re.search(r'剑指Offer[_-]*(\d+)', filename)
    if m:
        return f"剑指Offer {m.group(1)}"
    return None

def extract_problem_numbers_from_text(text, filepath=""):
    """从文档文本中精确提取题号引用，避免误报"""
    numbers = set()
    lines = text.split('\n')
    
    for line in lines:
        # Pattern 1: "LeetCode N" or "LeetCode N —" or "LeetCode N/" or "LeetCode N "
        for m in re.finditer(r'[Ll]eet[Cc]ode\s*(\d{1,4})(?:\s*[-/—]|\s+|$|\b)', line):
            n = int(m.group(1))
            if 1 <= n <= 2500 and not (2000 <= n <= 2099):
                numbers.add(n)
        
        # Pattern 2: "LC N" where N is a number (not part of a date)
        for m in re.finditer(r'\b[Ll][Cc]\s+(\d{1,4})\b', line):
            n = int(m.group(1))
            if 1 <= n <= 2500 and not (2000 <= n <= 2099):
                numbers.add(n)
        
        # Pattern 3: "lc0001" format in text
        for m in re.finditer(r'\blc0*(\d{1,4})\b', line, re.IGNORECASE):
            n = int(m.group(1))
            if 1 <= n <= 2500 and not (2000 <= n <= 2099):
                numbers.add(n)
        
        # Pattern 4: table rows that look like problem lists
        # e.g. | 1 | Two Sum | Easy |
        for m in re.finditer(r'\|\s*(\d{1,4})\s*\|\s*[^|]+\|\s*(?:Easy|Medium|Hard|简单|中等|困难)', line):
            n = int(m.group(1))
            if 1 <= n <= 2500 and not (2000 <= n <= 2099):
                numbers.add(n)
        
        # Pattern 5: "第N题" or "第 N 题"
        for m in re.finditer(r'第\s*(\d{1,4})\s*题', line):
            n = int(m.group(1))
            if 1 <= n <= 2500 and not (2000 <= n <= 2099):
                numbers.add(n)
    
    return numbers

def scan_code_files():
    """扫描所有代码文件"""
    code_index = defaultdict(lambda: {
        'rust': [],
        'python': [],
        'go': [],
        'lean': [],
        'c': [],
        'cpp': [],
        'java': [],
        'js': [],
        'ts': [],
    })
    
    leetcode_dirs = [
        (EXAMPLES_DIR / "algorithms/src/leetcode", 'rust'),
        (EXAMPLES_DIR / "algorithms-go/leetcode", 'go'),
        (EXAMPLES_DIR / "algorithms-python/leetcode", 'python'),
        (EXAMPLES_DIR / "algorithms-python/src/leetcode", 'python'),
        (EXAMPLES_DIR / "algorithms-rust/src/leetcode", 'rust'),
        (EXAMPLES_DIR / "lean_proofs/FormalAlgorithm/leetcode", 'lean'),
    ]
    
    for d, lang in leetcode_dirs:
        if not d.exists():
            continue
        for f in d.iterdir():
            if f.is_file() and f.suffix in ['.rs', '.go', '.py', '.lean', '.c', '.cpp', '.java', '.js', '.ts']:
                num = extract_problem_number_from_filename(f.name)
                if num and isinstance(num, int):
                    rel_path = f.relative_to(ROOT).as_posix()
                    code_index[num][lang].append(rel_path)
    
    return code_index

def scan_docs():
    """扫描文档文件"""
    doc_index = defaultdict(list)
    
    for doc_file in DOCS_DIR.rglob("*.md"):
        if doc_file.name == "README.md" or "99-附录" in str(doc_file):
            continue
        
        rel_path = doc_file.relative_to(ROOT).as_posix()
        text = doc_file.read_text(encoding='utf-8')
        numbers = extract_problem_numbers_from_text(text, str(doc_file))
        
        for num in numbers:
            if rel_path not in doc_index[num]:
                doc_index[num].append(rel_path)
    
    return doc_index

def load_known_problems():
    """加载已知的题目映射"""
    known = {
        1: ("Two Sum", "简单", "数组/哈希表"),
        3: ("Longest Substring Without Repeating Characters", "中等", "字符串/滑动窗口"),
        4: ("Median of Two Sorted Arrays", "困难", "数组/二分查找"),
        5: ("Longest Palindromic Substring", "中等", "字符串/动态规划"),
        9: ("Palindrome Number", "简单", "数学"),
        11: ("Container With Most Water", "中等", "数组/双指针"),
        15: ("3Sum", "中等", "数组/双指针"),
        17: ("Letter Combinations of a Phone Number", "中等", "字符串/回溯"),
        20: ("Valid Parentheses", "简单", "栈"),
        21: ("Merge Two Sorted Lists", "简单", "链表"),
        23: ("Merge k Sorted Lists", "困难", "链表/分治/堆"),
        26: ("Remove Duplicates from Sorted Array", "简单", "数组/双指针"),
        28: ("Implement strStr()", "简单", "字符串/KMP"),
        33: ("Search in Rotated Sorted Array", "中等", "数组/二分查找"),
        37: ("Sudoku Solver", "困难", "回溯"),
        39: ("Combination Sum", "中等", "数组/回溯"),
        42: ("Trapping Rain Water", "困难", "数组/双指针/动态规划"),
        45: ("Jump Game II", "中等", "数组/贪心/动态规划"),
        46: ("Permutations", "中等", "数组/回溯"),
        48: ("Rotate Image", "中等", "数组/数学"),
        50: ("Pow(x, n)", "中等", "数学/分治"),
        51: ("N-Queens", "困难", "回溯"),
        53: ("Maximum Subarray", "简单", "数组/动态规划/分治"),
        54: ("Spiral Matrix", "中等", "数组/模拟"),
        55: ("Jump Game", "中等", "数组/贪心/动态规划"),
        62: ("Unique Paths", "中等", "数组/动态规划/数学"),
        70: ("Climbing Stairs", "简单", "动态规划"),
        72: ("Edit Distance", "困难", "字符串/动态规划"),
        76: ("Minimum Window Substring", "困难", "字符串/滑动窗口/哈希表"),
        79: ("Word Search", "中等", "数组/回溯"),
        94: ("Binary Tree Inorder Traversal", "简单", "树/栈"),
        96: ("Unique Binary Search Trees", "中等", "树/动态规划/数学"),
        102: ("Binary Tree Level Order Traversal", "中等", "树/BFS"),
        104: ("Maximum Depth of Binary Tree", "简单", "树/DFS"),
        127: ("Word Ladder", "困难", "BFS"),
        133: ("Clone Graph", "中等", "图/DFS/BFS"),
        136: ("Single Number", "简单", "位运算"),
        137: ("Single Number II", "中等", "位运算"),
        141: ("Linked List Cycle", "简单", "链表/双指针"),
        142: ("Linked List Cycle II", "中等", "链表/双指针/数学"),
        153: ("Find Minimum in Rotated Sorted Array", "中等", "数组/二分查找"),
        155: ("Min Stack", "中等", "栈/设计"),
        167: ("Two Sum II - Input Array Is Sorted", "中等", "数组/双指针"),
        191: ("Number of 1 Bits", "简单", "位运算"),
        198: ("House Robber", "中等", "动态规划"),
        200: ("Number of Islands", "中等", "DFS/BFS/并查集"),
        204: ("Count Primes", "中等", "数学/质数筛"),
        206: ("Reverse Linked List", "简单", "链表"),
        207: ("Course Schedule", "中等", "图/拓扑排序/DFS"),
        209: ("Minimum Size Subarray Sum", "中等", "数组/前缀和/滑动窗口"),
        210: ("Course Schedule II", "中等", "图/拓扑排序"),
        226: ("Invert Binary Tree", "简单", "树/DFS"),
        232: ("Implement Queue using Stacks", "简单", "栈/队列/设计"),
        236: ("Lowest Common Ancestor of a Binary Tree", "中等", "树/DFS"),
        239: ("Sliding Window Maximum", "困难", "队列/滑动窗口/单调队列"),
        240: ("Search a 2D Matrix II", "中等", "数组/二分查找/分治"),
        260: ("Single Number III", "中等", "位运算"),
        300: ("Longest Increasing Subsequence", "中等", "数组/二分查找/动态规划"),
        312: ("Burst Balloons", "困难", "数组/动态规划"),
        322: ("Coin Change", "中等", "动态规划"),
        338: ("Counting Bits", "简单", "动态规划/位运算"),
        370: ("Range Addition", "中等", "数组/差分"),
        384: ("Shuffle an Array", "中等", "数组/随机/设计"),
        416: ("Partition Equal Subset Sum", "中等", "动态规划/背包问题"),
        435: ("Non-overlapping Intervals", "中等", "数组/贪心/动态规划"),
        455: ("Assign Cookies", "简单", "贪心/排序"),
        516: ("Longest Palindromic Subsequence", "中等", "字符串/动态规划"),
        523: ("Continuous Subarray Sum", "中等", "数组/哈希表/数学"),
        560: ("Subarray Sum Equals K", "中等", "数组/哈希表/前缀和"),
        583: ("Delete Operation for Two Strings", "中等", "字符串/动态规划"),
        704: ("Binary Search", "简单", "数组/二分查找"),
        743: ("Network Delay Time", "中等", "图/Dijkstra/最短路径"),
        787: ("Cheapest Flights Within K Stops", "中等", "图/动态规划/最短路径"),
        912: ("Sort an Array", "中等", "数组/排序/分治"),
        994: ("Rotting Oranges", "中等", "BFS"),
        1143: ("Longest Common Subsequence", "中等", "字符串/动态规划"),
        1584: ("Min Cost to Connect All Points", "中等", "图/最小生成树/Prim/Kruskal"),
        214: ("Shortest Palindrome", "困难", "字符串/KMP"),
        223: ("Rectangle Area", "中等", "数学/几何"),
        372: ("Super Pow", "中等", "数学/分治/模运算"),
        398: ("Random Pick Index", "中等", "数组/随机/蓄水池抽样"),
        470: ("Implement Rand10() Using Rand7()", "中等", "数学/概率/随机"),
        587: ("Erect the Fence", "困难", "数学/计算几何/凸包"),
        647: ("Palindromic Substrings", "中等", "字符串/动态规划/中心扩展"),
    }
    return known

def get_problem_title_from_filename(filename):
    """从代码文件名提取题目名称"""
    m = re.search(r'lc\d+_(.+?)\.\w+$', filename)
    if m:
        return m.group(1).replace('_', ' ').title()
    return ""

def classify_category(cat):
    """将细分类别归入大类"""
    if '数组' in cat or '矩阵' in cat:
        return '数组与矩阵'
    elif '链表' in cat:
        return '链表'
    elif '栈' in cat or '队列' in cat:
        return '栈与队列'
    elif '哈希' in cat:
        return '哈希表'
    elif '树' in cat or 'BST' in cat:
        return '二叉树与BST'
    elif '堆' in cat or '优先队列' in cat:
        return '堆与优先队列'
    elif '并查集' in cat:
        return '并查集'
    elif 'Trie' in cat or '字典树' in cat:
        return 'Trie树'
    elif any(k in cat for k in ['图', '拓扑', 'Dijkstra', 'Prim', 'Kruskal', '最短路径', '最小生成树', '连通分量']):
        return '图论'
    elif any(k in cat for k in ['字符串', 'KMP', '回文', '子序列', '子串']):
        return '字符串'
    elif any(k in cat for k in ['双指针', '滑动窗口', '前缀和', '差分', '二分', '枚举', '分治', '模拟']):
        return '算法范式'
    elif '贪心' in cat:
        return '贪心算法'
    elif any(k in cat for k in ['动态规划', 'DP', '背包']):
        return '动态规划'
    elif any(k in cat for k in ['回溯', 'DFS']):
        return '回溯与DFS'
    elif 'BFS' in cat:
        return 'BFS与图搜索'
    elif '位运算' in cat:
        return '位运算'
    elif any(k in cat for k in ['数学', '质数', 'GCD', 'LCM', '组合', '概率', '随机', '排序']):
        return '数学'
    else:
        return cat

def main():
    print("正在扫描代码文件...")
    code_index = scan_code_files()
    
    print("正在扫描文档...")
    doc_index = scan_docs()
    
    print("正在加载已知题目元数据...")
    known_problems = load_known_problems()
    
    # Build universe: all problems that have code OR have docs with known metadata
    all_code_problems = set(n for n in code_index.keys() if isinstance(n, int))
    all_doc_problems = set(n for n in doc_index.keys() if isinstance(n, int))
    all_known_problems = set(known_problems.keys())
    
    # Primary set: problems with code (the 77 covered problems)
    primary_problems = all_code_problems
    
    # Also include doc-only problems that have known metadata (legitimate references)
    extra_doc_problems = set()
    for n in all_doc_problems:
        if n not in primary_problems and n in all_known_problems:
            extra_doc_problems.add(n)
    
    all_problems = sorted(primary_problems | extra_doc_problems)
    
    # Build metadata
    meta = {}
    for num in all_problems:
        if num in known_problems:
            meta[num] = {
                'title': known_problems[num][0],
                'difficulty': known_problems[num][1],
                'category': known_problems[num][2],
            }
        else:
            # Try to infer from code filenames
            title = ""
            for lang_files in code_index.get(num, {}).values():
                for f in lang_files:
                    t = get_problem_title_from_filename(f)
                    if t:
                        title = t
                        break
                if title:
                    break
            meta[num] = {
                'title': title or f"Problem {num}",
                'difficulty': '未知',
                'category': '未分类',
            }
    
    # Build doc ownership
    doc_ownership = {}
    for num in all_doc_problems:
        docs = doc_index.get(num, [])
        if not docs:
            continue
        # Prefer specific topic docs over overview docs
        best = None
        for d in docs:
            if '导论' in d or '总览' in d or '方法论' in d:
                continue
            best = d
            break
        if not best and docs:
            best = docs[0]
        doc_ownership[num] = best
    
    # Stats
    total = len(all_problems)
    with_code = sum(1 for n in all_problems if any(code_index.get(n, {}).values()))
    with_lean = sum(1 for n in all_problems if code_index.get(n, {}).get('lean'))
    with_doc = sum(1 for n in all_problems if doc_index.get(n))
    fully_covered = sum(1 for n in all_problems if any(code_index.get(n, {}).values()) and doc_index.get(n))
    
    diff_counts = Counter(meta[n]['difficulty'] for n in all_problems if n in meta)
    
    cat_counts = Counter()
    for n in all_problems:
        if n in meta:
            cat_counts[classify_category(meta[n]['category'])] += 1
    
    lang_counts = {'Rust': 0, 'Python': 0, 'Go': 0, 'Lean': 0}
    for n in all_problems:
        if code_index.get(n, {}).get('rust'):
            lang_counts['Rust'] += 1
        if code_index.get(n, {}).get('python'):
            lang_counts['Python'] += 1
        if code_index.get(n, {}).get('go'):
            lang_counts['Go'] += 1
        if code_index.get(n, {}).get('lean'):
            lang_counts['Lean'] += 1
    
    print(f"统计: 总题数={total}, 有代码={with_code}, 有文档={with_doc}, 完全覆盖={fully_covered}, 有Lean={with_lean}")
    
    # Generate CSV
    print("生成 CSV 索引...")
    csv_rows = []
    for num in all_problems:
        m = meta.get(num, {})
        codes = code_index.get(num, {})
        docs = doc_index.get(num, [])
        doc_link = doc_ownership.get(num, '')
        
        row = {
            '题号': num,
            '题目名称': m.get('title', ''),
            '难度': m.get('difficulty', ''),
            '分类': m.get('category', '未分类'),
            '所属文档': doc_link,
            'Rust代码': ';'.join(codes.get('rust', [])),
            'Python代码': ';'.join(codes.get('python', [])),
            'Go代码': ';'.join(codes.get('go', [])),
            'Lean证明': ';'.join(codes.get('lean', [])),
            '是否有形式化证明': '是' if codes.get('lean') else '否',
        }
        csv_rows.append(row)
    
    with open(CSV_FILE, 'w', newline='', encoding='utf-8-sig') as f:
        writer = csv.DictWriter(f, fieldnames=[
            '题号', '题目名称', '难度', '分类', '所属文档',
            'Rust代码', 'Python代码', 'Go代码', 'Lean证明', '是否有形式化证明'
        ])
        writer.writeheader()
        writer.writerows(csv_rows)
    
    # Generate Appendix
    print("生成附录文件...")
    appendix_content = f"""# 附录一：LeetCode 题号全局索引

> 本索引由自动化脚本生成，覆盖 `docs/13-LeetCode算法面试专题/` 全部文档与 `examples/*` 下全部代码实现。
> 最后更新：2026-04-23

## 概览统计

| 指标 | 数值 |
|------|------|
| 索引题号总数 | {total} |
| 有代码实现 | {with_code} |
| 有文档覆盖 | {with_doc} |
| 代码+文档完全覆盖 | {fully_covered} |
| 有形式化证明 (Lean) | {with_lean} |

### 按难度分布

| 难度 | 数量 |
|------|------|
| 简单 | {diff_counts.get('简单', 0)} |
| 中等 | {diff_counts.get('中等', 0)} |
| 困难 | {diff_counts.get('困难', 0)} |
| 未知 | {diff_counts.get('未知', 0)} |

### 按数据结构/算法范式分布

| 分类 | 数量 |
|------|------|
"""
    for cat, cnt in sorted(cat_counts.items(), key=lambda x: -x[1]):
        appendix_content += f"| {cat} | {cnt} |\n"
    
    appendix_content += f"""
### 按语言覆盖

| 语言 | 实现题数 |
|------|----------|
| Rust | {lang_counts['Rust']} |
| Python | {lang_counts['Python']} |
| Go | {lang_counts['Go']} |
| Lean (形式化证明) | {lang_counts['Lean']} |

---

## 完整索引表

| 题号 | 题目名称 | 难度 | 分类 | 所属文档 | Rust | Python | Go | Lean证明 |
|------|----------|------|------|----------|------|--------|-----|----------|
"""
    
    for num in all_problems:
        m = meta.get(num, {})
        docs = doc_index.get(num, [])
        codes = code_index.get(num, {})
        doc_link = doc_ownership.get(num, '')
        if doc_link:
            doc_name = Path(doc_link).name.replace('.md', '')
            doc_cell = f"[{doc_name}](../{doc_link.replace('docs/13-LeetCode算法面试专题/', '').replace('.md', '.md')})"
        else:
            doc_cell = ""
        
        rust_mark = "✓" if codes.get('rust') else ""
        py_mark = "✓" if codes.get('python') else ""
        go_mark = "✓" if codes.get('go') else ""
        lean_mark = "✓" if codes.get('lean') else ""
        
        appendix_content += f"| {num} | {m.get('title', '')} | {m.get('difficulty', '')} | {m.get('category', '')} | {doc_cell} | {rust_mark} | {py_mark} | {go_mark} | {lean_mark} |\n"
    
    appendix_content += """
---

## 数据一致性审计

> 以下列出文档与代码之间的覆盖缺口，供后续补全参考。

### 仅有文档引用、无代码实现

以下题号在专题文档中被讨论或引用，但 `examples/` 下尚未找到对应代码实现：

"""
    
    doc_only = [n for n in sorted(all_doc_problems) if n not in primary_problems and n in all_known_problems]
    if doc_only:
        appendix_content += "| 题号 | 题目名称 | 所属文档 |\n|------|----------|----------|\n"
        for num in doc_only:
            m = known_problems.get(num, ('', '', ''))
            doc_link = doc_ownership.get(num, '')
            doc_name = Path(doc_link).name.replace('.md', '') if doc_link else ''
            appendix_content += f"| {num} | {m[0]} | {doc_name} |\n"
    else:
        appendix_content += "（无）\n"
    
    appendix_content += "\n### 仅有代码实现、无文档覆盖\n\n"
    appendix_content += "以下题号在 `examples/` 下有代码实现，但在专题文档中未被明确引用：\n\n"
    
    code_only = [n for n in sorted(primary_problems) if n not in all_doc_problems]
    if code_only:
        appendix_content += "| 题号 | 题目名称 | 代码文件 |\n|------|----------|----------|\n"
        for num in code_only:
            m = meta.get(num, {})
            first_code = ""
            for lang_files in code_index.get(num, {}).values():
                if lang_files:
                    first_code = Path(lang_files[0]).name
                    break
            appendix_content += f"| {num} | {m.get('title', '')} | {first_code} |\n"
    else:
        appendix_content += "（无）\n"
    
    appendix_content += """
### Lean 形式化证明清单

| 题号 | 题目名称 | Lean 文件 |
|------|----------|-----------|
"""
    lean_problems = [n for n in sorted(all_problems) if code_index.get(n, {}).get('lean')]
    for num in lean_problems:
        m = meta.get(num, {})
        lean_files = code_index.get(num, {}).get('lean', [])
        lean_names = ', '.join(Path(f).name for f in lean_files)
        appendix_content += f"| {num} | {m.get('title', '')} | {lean_names} |\n"
    
    APPENDIX_FILE.write_text(appendix_content, encoding='utf-8')
    
    # Generate README
    print("生成模块 README...")
    
    readme_content = f"""---
title: LeetCode算法面试专题目录 / LeetCode Algorithm Interview Specialization Index
version: 1.0
status: maintained
last_updated: 2026-04-23
owner: LeetCode面试专题工作组
concepts: ["面试准备", "算法实战", "LeetCode", "目录索引", "学习路径"]
level: 全级别
---

# LeetCode 算法面试专题

> 形式化算法库的核心实战模块，覆盖 LeetCode 高频面试题的形式化分析、多语言实现与严格证明。

## 模块简介

本专题将 LeetCode 经典面试题按**数据结构**、**算法范式**、**数学专题**、**字符串**、**图论**和**面试实战**六大板块进行系统梳理。每道题目均遵循「四步法」解题框架：

1. **形式化规约**：将题目转化为精确的数学描述；
2. **算法设计**：给出伪代码与复杂度分析；
3. **正确性证明**：使用循环不变式、归纳法或反证法证明；
4. **参考实现**：提供 Rust / Python / Go 等多语言代码。

此外，部分题目还配备了 **Lean 4 形式化证明**，确保证明的机器可检验性。

## 快速开始指南

### 阅读路线

| 读者背景 | 推荐阅读顺序 |
|----------|--------------|
| 算法初学者 | `00-总览与方法论` → `01-数据结构专题` → `02-算法范式专题` |
| 面试冲刺 | `06-面试专题` → `02-算法范式专题`（按需） |
| 形式化证明兴趣者 | `00-总览与方法论` → 任意专题中的「形式化证明」章节 → `lean_proofs/` |
| 多语言实践 | 阅读专题文档 → 对照 `examples/` 下对应语言的实现 |

### 目录结构

```
docs/13-LeetCode算法面试专题/
├── 00-总览与方法论/          # 3 篇：专题导论、解题四步法、复杂度速查
├── 01-数据结构专题/            # 9 篇：数组、链表、栈队列、哈希表、二叉树、堆、并查集、Trie
├── 02-算法范式专题/            # 12 篇：枚举、双指针、滑动窗口、前缀和、二分、分治、贪心、DP、回溯、BFS、位运算
├── 03-数学专题/               # 5 篇：数论、组合数学、计算几何、概率随机
├── 04-字符串专题/             # 4 篇：字符串匹配、回文问题、字符串DP
├── 05-图论专题/               # 5 篇：遍历、最短路径、拓扑排序、最小生成树
├── 06-面试专题/               # 6 篇：高频 Top 100、剑指 Offer、大厂真题
└── 99-附录/                  # 3 篇：题号全局索引、常见错误清单、代码模板速查
```

### 代码示例目录

```
examples/
├── algorithms/src/leetcode/        # Rust 实现（主仓库）
├── algorithms-rust/src/leetcode/   # Rust 补充实现
├── algorithms-python/src/leetcode/ # Python 实现
├── algorithms-go/leetcode/         # Go 实现
└── lean_proofs/leetcode/           # Lean 4 形式化证明
```

## 题号覆盖统计

- **索引题号总数**：{total}
- **代码实现题号数**：{with_code}
- **文档覆盖题号数**：{with_doc}
- **代码+文档完全覆盖**：{fully_covered}
- **形式化证明题号数**：{with_lean}

### 按难度分布

| 难度 | 数量 |
|------|------|
| 简单 | {diff_counts.get('简单', 0)} |
| 中等 | {diff_counts.get('中等', 0)} |
| 困难 | {diff_counts.get('困难', 0)} |

### 按算法范式/数据结构分布

| 分类 | 数量 |
|------|------|
"""
    for cat, cnt in sorted(cat_counts.items(), key=lambda x: -x[1]):
        readme_content += f"| {cat} | {cnt} |\n"
    
    readme_content += f"""
## 语言覆盖统计

| 语言 | 实现题数 | 说明 |
|------|----------|------|
| Rust | {lang_counts['Rust']} | 主要实现语言，包含在 `examples/algorithms/` |
| Python | {lang_counts['Python']} | 辅助教学语言，代码简洁易读 |
| Go | {lang_counts['Go']} | 工程实践语言，附带单测 |
| Lean 4 | {lang_counts['Lean']} | 形式化证明语言，机器可检验 |

## 形式化证明亮点

以下题目已完成 **Lean 4 形式化证明**，代表本模块在形式化验证方面的核心成果：

| 题号 | 题目名称 | 证明要点 |
|------|----------|----------|
| 1 | Two Sum | 解的存在性与唯一性条件 |
| 3 | Longest Substring Without Repeating Characters | 滑动窗口不变式 |
| 15 | 3Sum | 双指针正确性 |
| 21 | Merge Two Sorted Lists | 链表归并的终止性 |
| 53 | Maximum Subarray | Kadane 算法最优性子结构 |
| 70 | Climbing Stairs | 斐波那契递推的数学归纳 |
| 72 | Edit Distance | DP 状态转移正确性 |
| 104 | Maximum Depth of Binary Tree | 树高定义的递归等价 |
| 136 | Single Number | 异或运算的交换律与消去律 |
| 141 | Linked List Cycle | Floyd 判圈算法的正确性 |
| 198 | House Robber | DP 最优子结构归纳证明 |
| 200 | Number of Islands | DFS 连通分量计数 |
| 207 | Course Schedule | 拓扑排序与环检测的等价性 |
| 704 | Binary Search | 循环不变式与终止性 |

## 与外部资源的对齐表

### NeetCode 150

NeetCode 150 是业界广泛认可的刷题清单。以下是我们已覆盖的 NeetCode 题目：

| NeetCode 分类 | 本模块对应章节 | 覆盖题号示例 |
|---------------|----------------|--------------|
| Arrays & Hashing | `01-数据结构专题/04-哈希表` | 1, 136 |
| Two Pointers | `02-算法范式专题/02-双指针` | 11, 15, 26, 141, 142, 167 |
| Sliding Window | `02-算法范式专题/03-滑动窗口` | 3, 76, 209 |
| Stack | `01-数据结构专题/03-栈与队列` | 20, 155, 232 |
| Binary Search | `02-算法范式专题/05-二分查找` | 33, 153, 704 |
| Linked List | `01-数据结构专题/02-链表` | 21, 141, 142, 206 |
| Trees | `01-数据结构专题/05-二叉树与BST` | 94, 96, 102, 104, 226, 236 |
| Heap / Priority Queue | `01-数据结构专题/06-堆与优先队列` | 23, 239 |
| Backtracking | `02-算法范式专题/09-回溯与DFS` | 37, 39, 46, 51, 79 |
| Tries | `01-数据结构专题/08-Trie树` | — |
| Graphs | `05-图论专题` | 127, 133, 200, 207, 210, 743, 787, 994, 1584 |
| Advanced Graphs | `05-图论专题` | — |
| 1-D DP | `02-算法范式专题/08-动态规划` | 70, 198, 300, 322, 416 |
| 2-D DP | `02-算法范式专题/08-动态规划` | 72, 1143, 312 |
| Greedy | `02-算法范式专题/07-贪心算法` | 45, 55, 435, 455 |
| Intervals | `02-算法范式专题/07-贪心算法` | 435 |
| Math & Geometry | `03-数学专题` | 9, 48, 50, 204 |
| Bit Manipulation | `02-算法范式专题/11-位运算` | 136, 137, 191, 260, 338 |

### Blind 75

| Blind 75 分类 | 本模块对应章节 | 覆盖状态 |
|---------------|----------------|----------|
| Array | `01-数据结构专题/01-数组与矩阵` | 大部分覆盖 |
| Binary | `02-算法范式专题/05-二分查找` | 已覆盖 |
| DP | `02-算法范式专题/08-动态规划` | 已覆盖 |
| Graph | `05-图论专题` | 已覆盖 |
| Interval | `02-算法范式专题/07-贪心算法` | 已覆盖 |
| Linked List | `01-数据结构专题/02-链表` | 已覆盖 |
| Matrix | `01-数据结构专题/01-数组与矩阵` | 已覆盖 |
| String | `04-字符串专题` | 已覆盖 |
| Tree | `01-数据结构专题/05-二叉树与BST` | 已覆盖 |
| Heap | `01-数据结构专题/06-堆与优先队列` | 部分覆盖 |

### 剑指 Offer

| 剑指 Offer 题号 | 本模块位置 | 代码实现 |
|-----------------|------------|----------|
| 03 | `06-面试专题/04-剑指Offer精选形式化证明` | Python |
| 09 | `06-面试专题/04-剑指Offer精选形式化证明` | Go |
| 10-I | `06-面试专题/04-剑指Offer精选形式化证明` | Rust |

> 注：本模块的「剑指 Offer」部分侧重于**形式化证明**而非完整代码实现。

---

## 贡献指南

1. 新增题目请遵循 `lcXXXX_problem_name.rs` 的命名规范；
2. 文档中引用题号时，请确保在附录索引中同步更新；
3. 形式化证明优先使用 `lean_proofs/leetcode/` 目录；
4. 提交前运行 `scripts/generate_leetcode_index.py` 更新全局索引。
"""
    
    README_FILE.write_text(readme_content, encoding='utf-8')
    
    # Update PROJECT_STRUCTURE.md
    print("更新 PROJECT_STRUCTURE.md...")
    if PROJECT_STRUCTURE.exists():
        ps_text = PROJECT_STRUCTURE.read_text(encoding='utf-8')
    else:
        ps_text = ""
    
    leetcode_section = """### `docs/13-LeetCode算法面试专题/`

LeetCode 算法面试专题，形式化算法库的核心实战模块。按数据结构、算法范式、数学、字符串、图论、面试实战六大板块系统梳理 LeetCode 高频题。每道题遵循「四步法」框架（形式化规约→算法设计→正确性证明→参考实现），部分题目配备 Lean 4 形式化证明。配套代码分布在 `examples/algorithms/src/leetcode/` (Rust)、`examples/algorithms-python/src/leetcode/` (Python)、`examples/algorithms-go/leetcode/` (Go) 和 `examples/lean_proofs/leetcode/` (Lean)。

- `00-总览与方法论/` — 专题导论、解题四步法、复杂度速查与面试沟通模板
- `01-数据结构专题/` — 数组、链表、栈队列、哈希表、二叉树、堆、并查集、Trie
- `02-算法范式专题/` — 枚举、双指针、滑动窗口、前缀和、二分、分治、贪心、DP、回溯、BFS、位运算
- `03-数学专题/` — 数论、组合数学、计算几何、概率与随机算法
- `04-字符串专题/` — 字符串匹配与 KMP、回文问题、字符串动态规划
- `05-图论专题/` — 遍历、最短路径、拓扑排序、最小生成树
- `06-面试专题/` — 高频 Top 100、剑指 Offer 精选、大厂真题
- `99-附录/` — LeetCode 题号全局索引、常见错误清单、多语言代码模板速查
"""
    
    marker = "### `docs/13-LeetCode算法面试专题/"
    if marker in ps_text:
        # Replace existing section
        lines = ps_text.split('\n')
        new_lines = []
        in_section = False
        for line in lines:
            if line.strip().startswith(marker) or line.strip().startswith(marker.replace("###", "####")):
                in_section = True
                continue
            if in_section and (line.startswith("### ") or line.startswith("## ")):
                in_section = False
            if not in_section:
                new_lines.append(line)
        ps_text = '\n'.join(new_lines)
    
    # Insert before the last major section or append
    if "docs/" in ps_text:
        # Find last docs mention and insert after that section
        idx = ps_text.rfind("docs/")
        next_header = ps_text.find("\n## ", idx)
        if next_header == -1:
            ps_text = ps_text.rstrip() + "\n\n" + leetcode_section
        else:
            ps_text = ps_text[:next_header] + "\n\n" + leetcode_section + "\n\n" + ps_text[next_header:]
    else:
        ps_text = ps_text.rstrip() + "\n\n" + leetcode_section
    
    PROJECT_STRUCTURE.write_text(ps_text, encoding='utf-8')
    
    print("全部完成！")
    print(f"  - CSV 索引: {CSV_FILE}")
    print(f"  - 附录文件: {APPENDIX_FILE}")
    print(f"  - 模块 README: {README_FILE}")
    print(f"  - PROJECT_STRUCTURE: {PROJECT_STRUCTURE}")
    
    return {
        'doc_only': doc_only,
        'code_only': code_only,
        'total': total,
        'with_code': with_code,
        'with_doc': with_doc,
        'with_lean': with_lean,
        'fully_covered': fully_covered,
    }

if __name__ == "__main__":
    result = main()
    print("\n=== 审计结果 ===")
    print(f"总题数: {result['total']}")
    print(f"完全覆盖(代码+文档): {result['fully_covered']}")
    print(f"仅有文档无代码: {result['doc_only']}")
    print(f"仅有代码无文档: {result['code_only']}")
    print(f"有Lean证明: {result['with_lean']}")
