#!/usr/bin/env python3
"""
数学符号检查工具
检查LaTeX数学符号的规范性
"""

import re
from pathlib import Path
from typing import List, Tuple
from dataclasses import dataclass

@dataclass
class SymbolIssue:
    file: str
    line: int
    type: str
    message: str
    suggestion: str

# ISO 80000-2 推荐符号映射
ISO_RECOMMENDATIONS = {
    # 集合符号
    r'\\mathbb\{R\}': 'ℝ (实数集)',
    r'\\mathbb\{N\}': 'ℕ (自然数集)',
    r'\\mathbb\{Z\}': 'ℤ (整数集)',
    r'\\mathbb\{Q\}': 'ℚ (有理数集)',
    r'\\mathbb\{C\}': 'ℂ (复数集)',
}

# 常见符号错误和建议
COMMON_ISSUES = [
    {
        'pattern': r'\.\.\.',
        'context': r'\$[^$]*\.\.\.[^$]*\$',
        'message': '数学环境中使用 ...',
        'suggestion': '使用 \\cdots 代替 ...',
        'type': 'style'
    },
    {
        'pattern': r'<=',
        'context': r'\$[^$]*<=[^$]*\$',
        'message': '使用 <= 表示小于等于',
        'suggestion': '使用 \\leq 或 ≤',
        'type': 'error'
    },
    {
        'pattern': r'>=',
        'context': r'\$[^$]*>=[^$]*\$',
        'message': '使用 >= 表示大于等于',
        'suggestion': '使用 \\geq 或 ≥',
        'type': 'error'
    },
    {
        'pattern': r'\\to(?!ken)',
        'exclude': r'\\rightarrow',
        'message': '使用 \\to 表示箭头',
        'suggestion': '推荐使用 \\rightarrow 以提高可读性',
        'type': 'suggestion'
    },
    {
        'pattern': r'\\epsilon',
        'message': '使用 \\epsilon',
        'suggestion': '推荐使用 \\varepsilon 以区分元素符号',
        'type': 'suggestion'
    },
]

def check_math_in_file(file_path: Path) -> List[SymbolIssue]:
    """检查文件中的数学符号"""
    issues = []
    content = file_path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    for i, line in enumerate(lines, 1):
        # 检查是否在LaTeX数学环境中
        if '$' not in line:
            continue
        
        # 检查各种符号问题
        for issue in COMMON_ISSUES:
            pattern = issue.get('context', issue['pattern'])
            if re.search(pattern, line):
                # 检查排除项
                if 'exclude' in issue and re.search(issue['exclude'], line):
                    continue
                
                issues.append(SymbolIssue(
                    file=str(file_path),
                    line=i,
                    type=issue['type'],
                    message=issue['message'],
                    suggestion=issue['suggestion']
                ))
        
        # 检查希腊字母是否使用正确
        greek_issues = [
            (r'\\phi(?!l)', '\\varphi', 'phi vs varphi'),
            (r'\\theta(?!n)', '\\vartheta', 'theta vs vartheta'),
        ]
        
        for pattern, suggestion, desc in greek_issues:
            if re.search(pattern, line):
                issues.append(SymbolIssue(
                    file=str(file_path),
                    line=i,
                    type='suggestion',
                    message=f'使用 {desc}',
                    suggestion=f'考虑使用 {suggestion} 以提高一致性'
                ))
    
    return issues

def main():
    """主函数"""
    doc_path = Path('docs')
    all_issues = []
    
    md_files = list(doc_path.rglob('*.md'))
    
    for md_file in md_files:
        if '任务完成报告' in md_file.name:
            continue
        issues = check_math_in_file(md_file)
        all_issues.extend(issues)
    
    # 输出报告
    print("=" * 60)
    print("数学符号检查报告")
    print("=" * 60)
    print(f"检查文档数: {len(md_files)}")
    print(f"发现问题数: {len(all_issues)}")
    print()
    
    # 按类型统计
    error_count = sum(1 for i in all_issues if i.type == 'error')
    style_count = sum(1 for i in all_issues if i.type == 'style')
    suggestion_count = sum(1 for i in all_issues if i.type == 'suggestion')
    
    print(f"按类型分布:")
    print(f"  - 错误: {error_count}")
    print(f"  - 风格问题: {style_count}")
    print(f"  - 建议: {suggestion_count}")
    print()
    
    if all_issues:
        print("问题详情 (前20个):")
        print("-" * 60)
        for issue in all_issues[:20]:
            print(f"{issue.file}:{issue.line}")
            print(f"  [{issue.type}] {issue.message}")
            print(f"  建议: {issue.suggestion}")
            print()
    else:
        print("✅ 未发现明显问题")
    
    # 保存报告
    report_path = Path('docs/质量报告/math-symbol-check-report.md')
    report_lines = [
        "# 数学符号检查报告",
        "",
        f"生成时间: {__import__('datetime').datetime.now().isoformat()}",
        "",
        f"- 检查文档数: {len(md_files)}",
        f"- 发现问题数: {len(all_issues)}",
        f"- 错误: {error_count}",
        f"- 风格问题: {style_count}",
        f"- 建议: {suggestion_count}",
        "",
        "## 问题列表",
        "",
    ]
    
    for issue in all_issues:
        report_lines.append(f"### {issue.file}:{issue.line}")
        report_lines.append(f"- 类型: {issue.type}")
        report_lines.append(f"- 问题: {issue.message}")
        report_lines.append(f"- 建议: {issue.suggestion}")
        report_lines.append("")
    
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text('\n'.join(report_lines), encoding='utf-8')
    print(f"详细报告已保存: {report_path}")

if __name__ == '__main__':
    main()
