#!/usr/bin/env python3
"""
批量文档章节修复工具
为已有 YAML frontmatter 头但缺少标准章节的文档补充学习目标/参考文献/知识导航
"""

from pathlib import Path
from datetime import datetime


def has_yaml_header(content: str) -> bool:
    """检查是否有 YAML frontmatter"""
    return content.strip().startswith('---\n') or content.strip().startswith('---\r\n')


def has_standard_header(content: str) -> bool:
    """检查是否有标准六维头"""
    header_markers = ['**版本**', '**来源**', '**创建日期**', '**最后更新**', '**对齐日期**']
    first_30 = '\n'.join(content.split('\n')[:30])
    return any(m in first_30 for m in header_markers)


def missing_sections(content: str) -> list:
    """返回缺失的必需章节"""
    required = ['## 学习目标', '## 参考文献', '## 知识导航']
    return [s for s in required if s not in content]


def add_missing_sections(content: str, file_path: Path) -> str:
    """补充缺失章节"""
    lines = content.split('\n')
    
    # 找到文档末尾（跳过尾部空行）
    end_pos = len(lines)
    while end_pos > 0 and not lines[end_pos - 1].strip():
        end_pos -= 1
    
    additions = []
    if '## 学习目标' not in content:
        additions.extend([
            '',
            '---',
            '',
            '## 学习目标',
            '',
            '完成本章节后，读者将能够：',
            '1. 理解核心概念与基本原理',
            '2. 掌握关键定理与证明方法',
            '3. 应用所学知识解决实际问题',
            ''
        ])
    
    if '## 参考文献' not in content:
        additions.extend([
            '---',
            '',
            '## 参考文献',
            '',
            '- 待补充权威教材与论文引用',
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
    
    if not additions:
        return content
    
    new_lines = lines[:end_pos] + additions + lines[end_pos:]
    return '\n'.join(new_lines)


def main():
    root = Path(__file__).resolve().parent.parent
    doc_path = root / 'docs'
    
    core_dirs = [
        doc_path / '01-基础理论',
        doc_path / '03-形式化证明',
        doc_path / '04-算法复杂度',
        doc_path / '08-实现示例',
        doc_path / '10-高级主题',
    ]
    
    processed = 0
    skipped = 0
    
    for core_dir in core_dirs:
        if not core_dir.exists():
            continue
        for md_file in core_dir.rglob('*.md'):
            if any(skip in md_file.name for skip in ['README', '质量报告', '任务完成报告', '知识图谱']):
                continue
            
            content = md_file.read_text(encoding='utf-8')
            
            # 只处理有YAML头但无标准六维头，且缺少章节的文档
            if not has_yaml_header(content) or has_standard_header(content):
                skipped += 1
                continue
            
            missing = missing_sections(content)
            if not missing:
                skipped += 1
                continue
            
            new_content = add_missing_sections(content, md_file)
            md_file.write_text(new_content, encoding='utf-8')
            processed += 1
            if processed <= 5:
                print(f"✅ 已补充章节: {md_file.relative_to(root)} ({', '.join(missing)})")
    
    print(f"\n{'='*60}")
    print(f"批量章节修复完成")
    print(f"处理文档数: {processed}")
    print(f"跳过: {skipped}")


if __name__ == '__main__':
    main()
