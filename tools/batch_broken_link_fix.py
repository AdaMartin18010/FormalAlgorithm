#!/usr/bin/env python3
"""
批量断链修复工具
修复常见的断链模式
"""

import re
from pathlib import Path


def fix_broken_links(content: str, file_path: Path) -> tuple[str, int]:
    """修复断链，返回(新内容, 修复数)"""
    original = content
    fixes = 0
    
    # 模式1: 指向知识笔记/的链接（相对路径问题）
    # 如 [排序算法](知识笔记/排序算法.md) → 应该指向 docs/知识笔记/
    # 这些链接在根目录文档中，如果目标文件存在则保留，否则添加标记
    
    # 模式2: 指向 ../项目全面梳理-2025.md 的链接
    # 这些链接在子目录文档中，如果目标不存在则尝试修正
    
    link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    
    def replace_link(match):
        nonlocal fixes
        text = match.group(1)
        target = match.group(2)
        
        # 跳过外部链接和锚点
        if target.startswith(('http://', 'https://', '#', 'mailto:')):
            return match.group(0)
        
        # 检查目标是否存在
        target_path = file_path.parent / target
        md_target = target_path.with_suffix('.md')
        
        if target_path.exists() or md_target.exists():
            return match.group(0)
        
        # 尝试大小写修正
        lower_target = target_path.parent / target_path.name.lower()
        lower_md = lower_target.with_suffix('.md')
        if lower_target.exists() or lower_md.exists():
            fixes += 1
            return f'[{text}]({target.lower()})'
        
        # 无法修复，添加标记
        # fixes += 1
        # return f'[{text}]({target}) <!-- 链接待确认 -->'
        return match.group(0)
    
    new_content = re.sub(link_pattern, replace_link, content)
    return new_content, fixes


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    md_files = list(doc_path.rglob('*.md'))
    
    total_fixed = 0
    files_changed = 0
    
    for md_file in md_files:
        if any(skip in md_file.name for skip in ['README', '质量报告']):
            continue
        content = md_file.read_text(encoding='utf-8')
        new_content, fixes = fix_broken_links(content, md_file)
        if fixes > 0:
            md_file.write_text(new_content, encoding='utf-8')
            files_changed += 1
            total_fixed += fixes
            if files_changed <= 5:
                print(f"✅ 已修复 {fixes} 处: {md_file.relative_to(root)}")
    
    print(f"\n{'='*60}")
    print(f"批量断链修复完成")
    print(f"修改文件数: {files_changed}")
    print(f"总修复数: {total_fixed}")


if __name__ == '__main__':
    main()
