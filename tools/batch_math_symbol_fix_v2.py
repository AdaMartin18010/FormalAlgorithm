#!/usr/bin/env python3
"""
批量数学符号修复工具 v2
修复 error 和 style 级别的问题
"""

import re
from pathlib import Path


def fix_file(file_path: Path) -> int:
    """修复单个文件中的数学符号问题，返回修复数"""
    content = file_path.read_text(encoding='utf-8')
    original = content
    fixes = 0

    # 1. 修复数学环境中的 ... → \cdots（仅在 $...$ 内）
    def fix_dots(match):
        math = match.group(1)
        if '...' in math and '\\cdots' not in math and '\\ldots' not in math:
            return '$' + math.replace('...', '\\cdots') + '$'
        return match.group(0)

    new_content = re.sub(r'\$([^$]*?)\$', fix_dots, content)
    if new_content != content:
        fixes += content.count('...') - new_content.count('...')
        content = new_content

    # 2. 修复数学环境中的 <= → \leq
    def fix_leq(match):
        math = match.group(1)
        if '<=' in math and '\\leq' not in math:
            return '$' + math.replace('<=', '\\leq') + '$'
        return match.group(0)

    new_content = re.sub(r'\$([^$]*?)\$', fix_leq, content)
    if new_content != content:
        fixes += 1
        content = new_content

    # 3. 修复数学环境中的 >= → \geq
    def fix_geq(match):
        math = match.group(1)
        if '>=' in math and '\\geq' not in math:
            return '$' + math.replace('>=', '\\geq') + '$'
        return match.group(0)

    new_content = re.sub(r'\$([^$]*?)\$', fix_geq, content)
    if new_content != content:
        fixes += 1
        content = new_content

    if fixes > 0:
        file_path.write_text(content, encoding='utf-8')
    return fixes


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    md_files = list(doc_path.rglob('*.md'))

    total_fixed = 0
    files_changed = 0

    for md_file in md_files:
        if any(skip in md_file.name for skip in ['README', '质量报告', '任务完成报告']):
            continue
        fixes = fix_file(md_file)
        if fixes > 0:
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
