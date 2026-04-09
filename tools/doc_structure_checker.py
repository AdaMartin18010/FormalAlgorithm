#!/usr/bin/env python3
"""
文档结构检查工具
检查Markdown文档结构规范性
"""

import re
from pathlib import Path
from typing import List, Dict, Any
from dataclasses import dataclass, field
from datetime import datetime

@dataclass
class StructureIssue:
    file: str
    line: int
    type: str
    message: str

# 关键章节要求
REQUIRED_SECTIONS = {
    '标准文档': [
        '## 学习目标',
        '## 参考文献',
        '## 知识导航',
    ],
}

# 文档头必要字段
HEADER_FIELDS = ['版本', '创建日期', '最后更新']

def check_document_structure(file_path: Path) -> Dict[str, Any]:
    """检查文档结构"""
    result = {
        'file': str(file_path),
        'has_version_header': False,
        'missing_sections': [],
        'broken_links': [],
        'issues': [],
        'level': 'unknown',
    }
    
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        result['issues'].append(StructureIssue(
            file=str(file_path),
            line=0,
            type='error',
            message=f'无法读取文件: {e}'
        ))
        return result
    
    lines = content.split('\n')
    
    # 检查文档头
    header_pattern = r'^>\s*\*\*版本\*\*:\s*\d+\.\d+'
    if re.search(header_pattern, content, re.MULTILINE):
        result['has_version_header'] = True
    
    # 检查文档级别
    if '# ' in content[:500]:  # 一级标题
        result['level'] = 'main'
    elif '## ' in content[:500]:
        result['level'] = 'section'
    
    # 检查标准文档的必需章节
    if result['level'] == 'main':
        for section in REQUIRED_SECTIONS['标准文档']:
            if section not in content:
                result['missing_sections'].append(section)
    
    # 检查链接
    link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    for i, line in enumerate(lines, 1):
        for match in re.finditer(link_pattern, line):
            link_text = match.group(1)
            link_target = match.group(2)
            
            # 跳过外部链接和锚点
            if link_target.startswith(('http://', 'https://', '#')):
                continue
            
            # 检查内部链接
            target_path = file_path.parent / link_target
            if not target_path.exists() and not target_path.with_suffix('.md').exists():
                result['broken_links'].append({
                    'line': i,
                    'text': link_text,
                    'target': link_target,
                })
    
    # 检查标题层级
    heading_levels = []
    for i, line in enumerate(lines, 1):
        match = re.match(r'^(#{1,6})\s', line)
        if match:
            level = len(match.group(1))
            heading_levels.append((i, level))
    
    # 检查层级跳跃
    for i in range(1, len(heading_levels)):
        prev_level = heading_levels[i-1][1]
        curr_level = heading_levels[i][1]
        if curr_level > prev_level + 1:
            result['issues'].append(StructureIssue(
                file=str(file_path),
                line=heading_levels[i][0],
                type='warning',
                message=f'标题层级跳跃: 从{prev_level}级跳到{curr_level}级'
            ))
    
    return result

def main():
    """主函数"""
    doc_path = Path('docs')
    results = []
    
    md_files = list(doc_path.rglob('*.md'))
    
    for md_file in md_files:
        # 跳过某些文件
        if any(skip in str(md_file) for skip in ['任务完成报告', 'README', '质量报告']):
            continue
        result = check_document_structure(md_file)
        results.append(result)
    
    # 统计
    total = len(results)
    with_header = sum(1 for r in results if r['has_version_header'])
    with_missing_sections = sum(1 for r in results if r['missing_sections'])
    with_broken_links = sum(1 for r in results if r['broken_links'])
    with_issues = sum(1 for r in results if r['issues'])
    
    print("=" * 60)
    print("文档结构检查报告")
    print("=" * 60)
    print(f"检查文档数: {total}")
    print(f"有文档头: {with_header} ({with_header/total*100:.1f}%)")
    print(f"缺少章节: {with_missing_sections}")
    print(f"有断链: {with_broken_links}")
    print(f"有其他问题: {with_issues}")
    print()
    
    # 显示问题详情
    problem_files = [r for r in results if r['missing_sections'] or r['broken_links'] or r['issues']]
    
    if problem_files:
        print("问题详情 (前10个文件):")
        print("-" * 60)
        for result in problem_files[:10]:
            print(f"\n{result['file']}")
            if not result['has_version_header']:
                print("  ⚠️ 缺少文档头")
            if result['missing_sections']:
                print(f"  ⚠️ 缺少章节: {', '.join(result['missing_sections'])}")
            if result['broken_links']:
                print(f"  ⚠️ 断链数: {len(result['broken_links'])}")
                for link in result['broken_links'][:3]:
                    print(f"    - 行{link['line']}: [{link['text']}]({link['target']})")
            for issue in result['issues'][:3]:
                print(f"  [{issue.type}] 行{issue.line}: {issue.message}")
    else:
        print("✅ 未发现明显问题")
    
    # 保存报告
    report_path = Path('docs/质量报告/structure-check-report.md')
    report_lines = [
        "# 文档结构检查报告",
        "",
        f"生成时间: {datetime.now().isoformat()}",
        "",
        "## 统计",
        "",
        f"- 检查文档数: {total}",
        f"- 有文档头: {with_header} ({with_header/total*100:.1f}%)",
        f"- 缺少章节: {with_missing_sections}",
        f"- 有断链: {with_broken_links}",
        f"- 有其他问题: {with_issues}",
        "",
        "## 问题文件列表",
        "",
    ]
    
    for result in problem_files:
        report_lines.append(f"### {result['file']}")
        if not result['has_version_header']:
            report_lines.append("- ⚠️ 缺少文档头")
        for section in result['missing_sections']:
            report_lines.append(f"- ⚠️ 缺少章节: {section}")
        for link in result['broken_links']:
            report_lines.append(f"- ⚠️ 断链: 行{link['line']} [{link['text']}]({link['target']})")
        report_lines.append("")
    
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text('\n'.join(report_lines), encoding='utf-8')
    print(f"\n详细报告已保存: {report_path}")

if __name__ == '__main__':
    main()
