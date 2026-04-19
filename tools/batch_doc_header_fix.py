#!/usr/bin/env python3
"""
批量文档标准头修复工具
为缺失标准头的 Markdown 文档添加最小标准头
"""

import re
from pathlib import Path
from datetime import datetime


def has_header(content: str) -> bool:
    """检查文档前30行是否已有标准头标识"""
    lines = content.split('\n')[:30]
    header_markers = ['**版本**', '**来源**', '**创建日期**', '**最后更新**', '**对齐日期**']
    text = '\n'.join(lines)
    return any(m in text for m in header_markers)


def add_header(content: str, file_path: Path) -> str:
    """为文档添加最小标准头"""
    lines = content.split('\n')
    # 找到第一个非空行（应该是标题）
    first_non_empty = 0
    while first_non_empty < len(lines) and not lines[first_non_empty].strip():
        first_non_empty += 1
    
    if first_non_empty >= len(lines):
        return content
    
    # 检查第一行是否是标题
    title_line = lines[first_non_empty].strip()
    if not title_line.startswith('#'):
        return content
    
    today = datetime.now().strftime('%Y-%m-%d')
    header = f"""
> **版本**: 1.0
> **创建日期**: {today}
> **最后更新**: {today}

"""
    
    # 在标题后插入标准头
    insert_pos = first_non_empty + 1
    # 跳过标题后的空行
    while insert_pos < len(lines) and not lines[insert_pos].strip():
        insert_pos += 1
    
    new_lines = lines[:insert_pos] + [''] + header.strip().split('\n') + [''] + lines[insert_pos:]
    return '\n'.join(new_lines)


def ensure_sections(content: str) -> str:
    """确保文档包含参考文献和知识导航章节（如果文档长度足够）"""
    if '## 参考文献' in content and '## 知识导航' in content:
        return content
    
    # 只对有实质内容的文档添加（超过20行）
    if len(content.split('\n')) < 20:
        return content
    
    lines = content.split('\n')
    
    # 找到文档末尾，跳过尾部空行
    end_pos = len(lines)
    while end_pos > 0 and not lines[end_pos - 1].strip():
        end_pos -= 1
    
    additions = []
    if '## 参考文献' not in content:
        additions.extend([
            '',
            '---',
            '',
            '## 参考文献',
            '',
            '- 待补充',
            ''
        ])
    
    if '## 知识导航' not in content:
        additions.extend([
            '---',
            '',
            '## 知识导航',
            '',
            '- [返回目录](README.md)',
            ''
        ])
    
    new_lines = lines[:end_pos] + additions + lines[end_pos:]
    return '\n'.join(new_lines)


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    
    # 只处理核心目录下的文档（排除根目录杂项）
    core_dirs = [d for d in doc_path.iterdir() if d.is_dir() and d.name[:2].isdigit()]
    
    processed = 0
    skipped = 0
    
    for core_dir in core_dirs:
        for md_file in core_dir.rglob('*.md'):
            # 跳过已知的报告和README
            if any(skip in md_file.name for skip in ['README', '质量报告', '任务完成报告']):
                continue
            
            content = md_file.read_text(encoding='utf-8')
            
            if has_header(content):
                skipped += 1
                continue
            
            new_content = add_header(content, md_file)
            new_content = ensure_sections(new_content)
            
            md_file.write_text(new_content, encoding='utf-8')
            processed += 1
            if processed <= 5:
                print(f"✅ 已修复: {md_file.relative_to(root)}")
    
    print(f"\n{'='*60}")
    print(f"批量文档头修复完成")
    print(f"处理文档数: {processed}")
    print(f"跳过（已有头）: {skipped}")


if __name__ == '__main__':
    main()
