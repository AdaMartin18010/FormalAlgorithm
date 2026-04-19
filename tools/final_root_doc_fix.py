#!/usr/bin/env python3
"""
最终根目录文档扫尾
为根目录下可处理的文档添加标准头
"""

from pathlib import Path
from datetime import datetime


def has_header(content: str) -> bool:
    first_20 = '\n'.join(content.split('\n')[:20])
    markers = ['version:', '版本', '来源', '对齐日期', '创建日期']
    return any(m in first_20 for m in markers)


def add_header(content: str) -> str:
    lines = content.split('\n')
    today = datetime.now().strftime('%Y-%m-%d')
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    if first >= len(lines):
        return content
    title = lines[first].strip()
    if not title.startswith('#'):
        return content
    insert = first + 1
    while insert < len(lines) and not lines[insert].strip():
        insert += 1
    header = f"""
> **版本**: 1.0
> **创建日期**: {today}
> **最后更新**: {today}

"""
    return '\n'.join(lines[:insert] + [''] + header.strip().split('\n') + [''] + lines[insert:])


def ensure_sections(content: str) -> str:
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
    
    targets = [
        '内容补充标准-概念定义属性关系解释论证形式证明.md',
        '内容链接与补充完善方案-2025-02-02.md',
        '国际化推进计划.md',
        '学习路径设计.md',
        '实践指导手册.md',
        '引用数据库扩展报告-2025.md',
        '引用规范与数据库.md',
        '思维表征模板集.md',
        '数学符号标准化规范.md',
        '数学符号规范.md',
        '文件清理完成报告-2025-11-14.md',
    ]
    
    processed = 0
    for name in targets:
        f = doc_path / name
        if not f.exists():
            continue
        content = f.read_text(encoding='utf-8')
        if has_header(content):
            continue
        new_content = add_header(content)
        new_content = ensure_sections(new_content)
        f.write_text(new_content, encoding='utf-8')
        processed += 1
        print(f"✅ 已修复: {name}")
    
    print(f"\n{'='*60}")
    print(f"根目录文档扫尾完成")
    print(f"处理文档数: {processed}")


if __name__ == '__main__':
    main()
