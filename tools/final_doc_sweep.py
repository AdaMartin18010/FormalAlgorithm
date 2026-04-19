#!/usr/bin/env python3
"""
最终文档扫尾脚本
为剩余可处理文档批量补全标准头
"""

from pathlib import Path
from datetime import datetime


def has_any_header(content: str) -> bool:
    """检查是否有任何形式的文档头"""
    first_30 = '\n'.join(content.split('\n')[:30])
    markers = ['version:', '版本', '来源', '对齐日期', '创建日期', '**Version**', '**Source**']
    return any(m in first_30 for m in markers)


def add_header(content: str, file_path: Path) -> str:
    """添加标准头"""
    lines = content.split('\n')
    today = datetime.now().strftime('%Y-%m-%d')
    
    # 找到第一个非空行
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    
    if first >= len(lines):
        return content
    
    # 如果第一行是标题，在标题后插入
    title_line = lines[first].strip()
    if title_line.startswith('#'):
        insert_pos = first + 1
        while insert_pos < len(lines) and not lines[insert_pos].strip():
            insert_pos += 1
        
        header = f"""
> **版本**: 1.0
> **创建日期**: {today}
> **最后更新**: {today}

"""
        new_lines = lines[:insert_pos] + [''] + header.strip().split('\n') + [''] + lines[insert_pos:]
        return '\n'.join(new_lines)
    
    return content


def ensure_sections(content: str) -> str:
    """确保有参考文献和知识导航"""
    if len(content.split('\n')) < 15:
        return content
    
    additions = []
    if '## 参考文献' not in content:
        additions.extend(['', '---', '', '## 参考文献', '', '- 待补充', ''])
    if '## 知识导航' not in content:
        additions.extend(['---', '', '## 知识导航', '', '- [返回目录](README.md)', ''])
    
    if not additions:
        return content
    
    lines = content.split('\n')
    end = len(lines)
    while end > 0 and not lines[end - 1].strip():
        end -= 1
    
    return '\n'.join(lines[:end] + additions + lines[end:])


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    
    # 目标目录（排除内部报告目录）
    target_dirs = [
        doc_path / '03-形式化证明',
        doc_path / '05-类型理论',
        doc_path / '10-高级主题',
        doc_path / '知识图谱',
        doc_path / 'international_alignment',
        doc_path / '交叉索引',
        doc_path / '国际化',
        doc_path / '实战案例',
        doc_path / '模板',
        doc_path / '片段库',
    ]
    
    processed = 0
    skipped = 0
    
    for td in target_dirs:
        if not td.exists():
            continue
        for md_file in td.rglob('*.md'):
            if 'README' in md_file.name:
                continue
            content = md_file.read_text(encoding='utf-8')
            if has_any_header(content):
                skipped += 1
                continue
            
            new_content = add_header(content, md_file)
            new_content = ensure_sections(new_content)
            md_file.write_text(new_content, encoding='utf-8')
            processed += 1
            if processed <= 5:
                print(f"✅ 已修复: {md_file.relative_to(root)}")
    
    print(f"\n{'='*60}")
    print(f"最终文档扫尾完成")
    print(f"处理文档数: {processed}")
    print(f"跳过（已有头）: {skipped}")


if __name__ == '__main__':
    main()
