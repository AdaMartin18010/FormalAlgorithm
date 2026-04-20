#!/usr/bin/env python3
"""Batch add frontmatter and refresh dates for core documents."""

import os
import re
from pathlib import Path
from datetime import datetime

# Knowledge concepts mapping for core modules
MODULE_CONCEPTS = {
    "01-基础理论": ["集合论", "数理逻辑", "代数结构", "函数论", "数论", "概率统计", "信息论"],
    "02-递归理论": ["递归函数", "原始递归", "可计算性", "停机问题", "递归可枚举"],
    "03-形式化证明": ["证明系统", "霍尔逻辑", "归纳法", "构造性证明", "反证法", "SMT"],
    "04-算法复杂度": ["时间复杂度", "空间复杂度", "渐进分析", "复杂度类", "主定理", "摊还分析"],
    "05-类型理论": ["简单类型", "多态类型", "依赖类型", "同伦类型论", "类型推导"],
    "06-逻辑系统": ["命题逻辑", "谓词逻辑", "模态逻辑", "直觉逻辑", "线性逻辑", "时序逻辑"],
    "07-计算模型": ["图灵机", "λ演算", "自动机", "量子计算", "细胞自动机", "神经网络"],
    "08-实现示例": ["Rust", "Lean4", "Haskell", "形式化验证", "程序提取"],
    "09-算法理论": ["排序", "搜索", "图算法", "动态规划", "贪心", "分治", "回溯", "随机算法"],
    "10-高级主题": ["量子算法", "机器学习", "并行计算", "流算法", "分布式算法"],
    "12-应用领域": ["人工智能", "区块链", "网络安全", "生物信息学", "金融", "量子应用"],
}

def get_module_concepts(filepath):
    for mod, concepts in MODULE_CONCEPTS.items():
        if mod in str(filepath):
            return concepts[:5]
    return []

def add_frontmatter_and_refresh(filepath):
    try:
        content = filepath.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        try:
            content = filepath.read_text(encoding="utf-16")
        except Exception:
            return False
    
    # Skip if not markdown
    if filepath.suffix != ".md":
        return False
    
    # Skip reports and templates
    if "项目改进" in str(filepath) or "项目扩展" in str(filepath) or "报告" in str(filepath):
        return False
    
    concepts = get_module_concepts(filepath)
    today = datetime.now().strftime("%Y-%m-%d")
    
    if content.startswith("---"):
        # Has frontmatter
        end = content.find("---", 3)
        if end != -1:
            fm = content[3:end].strip()
            body = content[end+3:]
            
            # Add concepts if missing
            if concepts and "concepts:" not in fm:
                concepts_str = ", ".join(f'"{c}"' for c in concepts)
                fm += f"\nconcepts: [{concepts_str}]"
            
            # Add level if missing
            if "level:" not in fm:
                fm += "\nlevel: 中级"
            
            # Refresh date
            if "last_updated:" in fm:
                fm = re.sub(r'last_updated:\s*\d{4}-\d{2}-\d{2}', f'last_updated: {today}', fm)
            elif "创建日期" not in fm and "创建" not in fm:
                fm += f"\nlast_updated: {today}"
            
            new_content = f"---\n{fm}\n---\n{body}"
            filepath.write_text(new_content, encoding="utf-8")
            return True
    else:
        # No frontmatter - add minimal one
        if concepts:
            concepts_str = ", ".join(f'"{c}"' for c in concepts)
            title = filepath.stem.replace("-", " ").replace("_", " ")
            fm = f"""---
title: {title}
concepts: [{concepts_str}]
level: 中级
last_updated: {today}
---

"""
            filepath.write_text(fm + content, encoding="utf-8")
            return True
    return False

def main():
    base = Path("docs")
    processed = 0
    
    # Process core module docs
    for mod_dir in base.iterdir():
        if not mod_dir.is_dir():
            continue
        name = mod_dir.name
        if not (name.startswith("0") or name.startswith("1") or name.startswith("2")):
            continue
        
        for md_file in mod_dir.rglob("*.md"):
            if add_frontmatter_and_refresh(md_file):
                processed += 1
                if processed % 50 == 0:
                    print(f"Processed {processed} documents...")
    
    print(f"\nTotal processed: {processed}")

if __name__ == "__main__":
    main()
