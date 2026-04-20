#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念引用替换 - V3 行级匹配策略
"""
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

for concept, authority in CONCEPTS.items():
    authority_path = DOCS_DIR / authority.replace("docs/", "")
    escaped = re.escape(concept)
    
    # 定义起始行的模式
    start_patterns = [
        re.compile(r'^' + escaped + r'\s*[(（].*?[）)]\s*[：:是为指].*'),
        re.compile(r'^' + escaped + r'\s*[：:是为指].*'),
        re.compile(r'^\*\*' + escaped + r'\*\*.*?[：:是为指].*'),
        re.compile(r'^\*\*定义\s*[\d\.]*\s*\*\*\s*[(（]?' + escaped + r'[）)]?.*'),
        re.compile(r'^\*\*' + escaped + r'定义\s*/\s*Definition.*'),
    ]
    
    for md_file in DOCS_DIR.rglob("*.md"):
        if md_file == authority_path:
            continue
        if "示例库" in str(md_file):
            continue
        skip_dirs = ["项目改进", "项目进度", "项目完成报告", "阶段报告", "引用数据库", "任务完成报告", "内容去重"]
        if any(d in str(md_file) for d in skip_dirs):
            continue
        
        try:
            lines = md_file.read_text(encoding="utf-8").splitlines()
        except Exception:
            continue
        
        new_lines = []
        i = 0
        changed = False
        
        while i < len(lines):
            line = lines[i]
            matched = False
            
            for sp in start_patterns:
                if sp.match(line.strip()):
                    # 找到了定义起始行，收集后续内容直到遇到空行、标题行或结束标志
                    definition_lines = [line]
                    j = i + 1
                    while j < len(lines):
                        next_line = lines[j]
                        # 停止条件：空行、标题行、分隔线、或另一个定义行
                        if next_line.strip() == '' or next_line.strip().startswith('#') or next_line.strip().startswith('---'):
                            break
                        # 如果遇到另一个 "定义" 或 "定理" 开头，也停止
                        if re.match(r'^\*\*(定义|定理|引理|公理)', next_line.strip()):
                            break
                        definition_lines.append(next_line)
                        j += 1
                    
                    # 只有定义段落足够长才替换
                    definition_text = '\n'.join(definition_lines)
                    if len(definition_text) >= 50 and len(definition_text) <= 1200:
                        if "权威定义参见主文档" not in definition_text:
                            replacement = f"> **概念**: [{concept}]({authority}) 的权威定义参见主文档。"
                            new_lines.append(replacement)
                            # 跳过已消费的行
                            i = j
                            changed = True
                            replaced_count += 1
                            matched = True
                            break
                    # 不够长或不满足条件，保留原行
                    break
            
            if not matched:
                new_lines.append(line)
                i += 1
        
        if changed:
            md_file.write_text('\n'.join(new_lines) + '\n', encoding="utf-8")
            replaced_files.add(str(md_file.relative_to(WORK_DIR)))

print(f"概念引用替换完成：覆盖了 {len(replaced_files)} 个文件，共 {replaced_count} 处替换。")
print(f"\n被替换的文件列表：")
for f in sorted(list(replaced_files)):
    print(f"  - {f}")
