#!/usr/bin/env python3
"""
引用检查工具
检查文档中的学术引用规范性
"""

import re
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict
import json

@dataclass
class CitationIssue:
    file: str
    line: int
    type: str
    message: str

def extract_reference_ids(db_path: Path) -> Dict[str, dict]:
    """从引用数据库中提取引用ID"""
    ref_ids = {}
    
    # 尝试读取YAML格式的引用数据库
    try:
        import yaml
        content = db_path.read_text(encoding='utf-8')
        # 提取所有reference_id
        for match in re.finditer(r'reference_id:\s*"([^"]+)"', content):
            ref_ids[match.group(1)] = {}
    except ImportError:
        # 如果没有yaml库，使用简单正则提取
        content = db_path.read_text(encoding='utf-8')
        for match in re.finditer(r'reference_id:\s*"([^"]+)"', content):
            ref_ids[match.group(1)] = {}
    
    return ref_ids

def check_citations_in_file(file_path: Path) -> List[CitationIssue]:
    """检查单个文件的引用"""
    issues = []
    content = file_path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    # 检查定义后是否有引用
    definition_patterns = [
        r'\*\*定义\s*\(\s*[^)]+\)\s*\*\*',
        r'\*\*Definition\s*\(\s*[^)]+\)\s*\*\*',
        r'#### 定义[:：]',
    ]
    
    for i, line in enumerate(lines, 1):
        for pattern in definition_patterns:
            if re.search(pattern, line, re.IGNORECASE):
                # 检查接下来的5行内是否有引用
                next_lines = '\n'.join(lines[i:i+5])
                if not re.search(r'\[[A-Z][a-zA-Z]+\s*\d{4}\]', next_lines):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='missing',
                        message=f'定义后可能缺少引用: {line[:60]}...'
                    ))
                break
    
    # 检查定理后是否有引用
    theorem_patterns = [
        r'\*\*定理\s*\(\s*[^)]+\)\s*\*\*',
        r'\*\*Theorem\s*\(\s*[^)]+\)\s*\*\*',
    ]
    
    for i, line in enumerate(lines, 1):
        for pattern in theorem_patterns:
            if re.search(pattern, line, re.IGNORECASE):
                next_lines = '\n'.join(lines[i:i+5])
                if not re.search(r'\[[A-Z][a-zA-Z]+\s*\d{4}\]', next_lines):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='missing',
                        message=f'定理后可能缺少引用: {line[:60]}...'
                    ))
                break
    
    # 检查引用格式
    citation_pattern = r'\[([A-Z][a-zA-Z]+)\s*(\d{4})\]'
    for i, line in enumerate(lines, 1):
        for match in re.finditer(citation_pattern, line):
            citation_key = f"{match.group(1)}{match.group(2)}"
            # 这里可以检查引用ID是否在数据库中
            # 暂时跳过具体ID检查
    
    return issues

def main():
    """主函数"""
    doc_path = Path('docs')
    
    # 尝试加载引用数据库
    ref_db_paths = [
        Path('docs/引用数据库-扩展版-2025.md'),
        Path('docs/引用数据库-核心算法-2025.md'),
    ]
    
    ref_db = {}
    for db_path in ref_db_paths:
        if db_path.exists():
            ref_db.update(extract_reference_ids(db_path))
    
    all_issues = []
    md_files = list(doc_path.rglob('*.md'))
    
    for md_file in md_files:
        # 跳过某些文件
        if '任务完成报告' in md_file.name or 'README' in md_file.name:
            continue
        issues = check_citations_in_file(md_file)
        all_issues.extend(issues)
    
    # 输出报告
    print("=" * 60)
    print("引用检查报告")
    print("=" * 60)
    print(f"检查文档数: {len(md_files)}")
    print(f"发现问题数: {len(all_issues)}")
    print(f"引用数据库条目: {len(ref_db)}")
    print()
    
    if all_issues:
        print("前20个问题:")
        print("-" * 60)
        for issue in all_issues[:20]:
            print(f"{issue.file}:{issue.line}")
            print(f"  [{issue.type}] {issue.message}")
            print()
    else:
        print("✅ 未发现明显问题")
    
    # 保存详细报告
    report_path = Path('docs/质量报告/citation-check-report.md')
    report_lines = [
        "# 引用检查报告",
        "",
        f"生成时间: {__import__('datetime').datetime.now().isoformat()}",
        "",
        f"- 检查文档数: {len(md_files)}",
        f"- 发现问题数: {len(all_issues)}",
        "",
        "## 问题列表",
        "",
    ]
    
    for issue in all_issues:
        report_lines.append(f"### {issue.file}:{issue.line}")
        report_lines.append(f"- 类型: {issue.type}")
        report_lines.append(f"- 信息: {issue.message}")
        report_lines.append("")
    
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text('\n'.join(report_lines), encoding='utf-8')
    print(f"\n详细报告已保存: {report_path}")

if __name__ == '__main__':
    main()
