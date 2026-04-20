#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念引用替换 - V2 更激进策略
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
    
    # 构建多种匹配模式
    escaped = re.escape(concept)
    patterns = [
        # 模式1: 概念名（可选英文）是/定义为/指 开头，后跟多行详细解释
        (r'(?:^|\n)({}\s*[(（][^）)]+[）)]\s*[：:是为指].*?\n(?:[^\n#].*?\n){{2,12}})'.format(escaped)),
        # 模式2: 概念名 是/定义为/指 开头
        (r'(?:^|\n)({}\s*[：:是为指].*?\n(?:[^\n#].*?\n){{2,12}})'.format(escaped)),
        # 模式3: **概念名** ... 是/定义为/指
        (r'(?:^|\n)(\*\*{}\*\*.*?[：:是为指].*?\n(?:[^\n#].*?\n){{2,12}})'.format(escaped)),
        # 模式4: **定义** ... 概念名 ... (多行解释，非单行)
        (r'(?:^|\n)(\*\*定义\s*[\d\.]*\s*\*\*.*?{}.*?\n(?:[^\n#].*?\n){{3,15}})'.format(escaped)),
    ]
    
    for md_file in DOCS_DIR.rglob("*.md"):
        if md_file == authority_path:
            continue
        if "示例库" in str(md_file):
            continue
        # 跳过项目管理和报告类文档
        skip_dirs = ["项目维护", "项目改进", "项目进度", "项目完成报告", "阶段报告", "引用数据库", "任务完成报告"]
        if any(d in str(md_file) for d in skip_dirs):
            continue
        
        try:
            text = md_file.read_text(encoding="utf-8")
        except Exception:
            continue
        
        new_text = text
        changed = False
        
        for pattern_str in patterns:
            pattern = re.compile(pattern_str, re.MULTILINE)
            matches = list(pattern.finditer(new_text))
            for m in reversed(matches):
                # 确保匹配到的内容足够长（是详细定义，不是简单提及）
                matched_text = m.group(1)
                if len(matched_text) < 40:  # 太短的跳过
                    continue
                # 避免替换已经是指引链接的内容
                if "权威定义参见主文档" in matched_text:
                    continue
                # 替换
                replacement = f"> **概念**: [{concept}]({authority}) 的权威定义参见主文档。\n\n"
                new_text = new_text[:m.start(1)] + replacement + new_text[m.end(1):]
                changed = True
                replaced_count += 1
        
        if changed:
            md_file.write_text(new_text, encoding="utf-8")
            replaced_files.add(str(md_file.relative_to(WORK_DIR)))

print(f"概念引用替换完成：覆盖了 {len(replaced_files)} 个文件，共 {replaced_count} 处替换。")
print(f"\n被替换的文件列表（前30）：")
for f in sorted(list(replaced_files))[:30]:
    print(f"  - {f}")
