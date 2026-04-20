#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念引用替换 - 增强版
"""
import os
import re
from pathlib import Path

WORK_DIR = Path("G:/_src/FormalAlgorithm")
DOCS_DIR = WORK_DIR / "docs"

CONCEPTS = {
    "图灵机": "docs/07-计算模型/01-图灵机.md",
    "递归函数": "docs/02-递归理论/01-递归函数定义.md",
    "BQP类": "docs/04-算法复杂度/04-复杂度类.md",
    "同伦类型论": "docs/05-类型理论/03-同伦类型论.md",
    "动态规划": "docs/09-算法理论/01-算法基础/06-动态规划理论.md",
    "量子纠缠": "docs/07-计算模型/05-量子计算模型.md",
    "类型系统": "docs/05-类型理论/04-类型系统.md",
    "证明助手": "docs/08-实现示例/04-形式化验证.md",
}

alt_type_system = DOCS_DIR / "05-类型理论" / "04-类型系统.md"
if not alt_type_system.exists():
    CONCEPTS["类型系统"] = "docs/05-类型理论/01-简单类型论-六维补充.md"

replaced_count = 0
replaced_files = set()

# 更宽松的定义匹配模式
# 使用 %s 占位符避免 format 的 keyerror 问题

definition_patterns = [
    # 模式A: **定义 X.X** (概念名) ... 后面跟多行
    r'(?:^|\n)(\*\*定义\s*[\d\.]*\s*\*\*\s*\(?\s*%s\s*\)?.*?\n(?:[^\n#].*?\n){2,15})',
    # 模式B: 概念名 是/指/定义为 ... 长解释
    r'(?:^|\n)(%s\s*[:：是指定义为].*?\n(?:[^\n#].*?\n){2,15})',
    # 模式C: **概念名** ... 定义 ... 长解释
    r'(?:^|\n)(\*\*%s\*\*.*?定义.*?\n(?:[^\n#].*?\n){2,15})',
]

for concept, authority in CONCEPTS.items():
    authority_path = DOCS_DIR / authority.replace("docs/", "")
    for md_file in DOCS_DIR.rglob("*.md"):
        if md_file == authority_path:
            continue
        if "示例库" in str(md_file):
            continue
        if "项目改进" in str(md_file) and md_file.name == "内容去重执行记录.md":
            continue
        # 跳过非内容文档
        skip_dirs = ["项目维护", "项目改进", "项目进度", "项目完成报告", "阶段报告", "引用数据库"]
        if any(d in str(md_file) for d in skip_dirs):
            continue
        
        try:
            text = md_file.read_text(encoding="utf-8")
        except Exception:
            continue
        
        new_text = text
        changed = False
        
        for pattern_template in definition_patterns:
            escaped = re.escape(concept)
            pattern_str = pattern_template % escaped
            pattern = re.compile(pattern_str, re.MULTILINE)
            matches = list(pattern.finditer(new_text))
            for m in reversed(matches):
                # 构造替换文本
                replacement = f"> **概念**: [{concept}]({authority}) 的权威定义参见主文档。\n\n"
                new_text = new_text[:m.start(1)] + replacement + new_text[m.end(1):]
                changed = True
                replaced_count += 1
        
        if changed:
            md_file.write_text(new_text, encoding="utf-8")
            replaced_files.add(str(md_file.relative_to(WORK_DIR)))

print(f"概念引用替换完成：覆盖了 {len(replaced_files)} 个文件，共 {replaced_count} 处替换。")

# 输出被替换的文件列表
print("\n被替换的文件列表：")
for f in sorted(replaced_files):
    print(f"  - {f}")
