#!/usr/bin/env python3
"""
批量数学符号修复工具
修复常见的数学符号风格问题
"""

import re
from pathlib import Path


def fix_math_symbols(content: str) -> tuple[str, int]:
    """修复数学符号问题，返回(新内容, 修复数)"""
    original = content
    fixes = 0
    
    # 1. 数学环境中的 ... → \cdots（仅在 $...$ 内）
    # 匹配 $...$ 块中的 ...
    def fix_dots_in_math(match):
        math_content = match.group(1)
        if '...' in math_content and '\cdots' not in math_content and '\ldots' not in math_content:
            return '$' + math_content.replace('...', '\\cdots') + '$'
        return match.group(0)
    
    new_content = re.sub(r'\$([^$]*?)\$', fix_dots_in_math, content)
    if new_content != content:
        fixes += content.count('...') - new_content.count('...')
        content = new_content
    
    # 2. 数学环境中的 <= → \leq
    def fix_leq_in_math(match):
        math_content = match.group(1)
        if '<=' in math_content and '\leq' not in math_content:
            return '$' + math_content.replace('<=', '\\leq') + '$'
        return match.group(0)
    
    new_content = re.sub(r'\$([^$]*?)\$', fix_leq_in_math, content)
    if new_content != content:
        fixes += 1
        content = new_content
    
    # 3. 数学环境中的 >= → \geq
    def fix_geq_in_math(match):
        math_content = match.group(1)
        if '>=' in math_content and '\geq' not in math_content:
            return '$' + math_content.replace('>=', '\\geq') + '$'
        return match.group(0)
    
    new_content = re.sub(r'\$([^$]*?)\$', fix_geq_in_math, content)
    if new_content != content:
        fixes += 1
        content = new_content
    
    # 4. 中文标点出现在数学环境中（顿号、句号等）
    # 暂不处理，避免误伤
    
    return content, fixes


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    
    md_files = list(doc_path.rglob('*.md'))
    total_fixed = 0
    files_changed = 0
    
    for md_file in md_files:
        if any(skip in md_file.name for skip in ['README', '质量报告', '任务完成报告']):
            continue
        
        content = md_file.read_text(encoding='utf-8')
        new_content, fixes = fix_math_symbols(content)
        
        if fixes > 0:
            md_file.write_text(new_content, encoding='utf-8')
            files_changed += 1
            total_fixed += fixes
            if files_changed <= 5:
                print(f"✅ 已修复 {fixes} 处: {md_file.relative_to(root)}")
    
    print(f"\n{'='*60}")
    print(f"批量数学符号修复完成")
    print(f"修改文件数: {files_changed}")
    print(f"总修复数: {total_fixed}")


if __name__ == '__main__':
    main()
