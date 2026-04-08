#!/usr/bin/env python3
"""
数学符号检查工具
检查LaTeX数学符号的规范性

功能：
- 检查数学符号是否符合ISO 80000-2
- 检查常见符号错误
- 检查公式排版
"""

import re
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Set, Tuple
from collections import defaultdict
import sys


@dataclass
class MathSymbolIssue:
    """数学符号问题记录"""
    file: str
    line: int
    type: str  # 'symbol', 'format', 'style', 'consistency'
    severity: str  # 'error', 'warning', 'info'
    message: str
    suggestion: str = ""
    context: str = ""


# ISO 80000-2 推荐符号
ISO_RECOMMENDED_SYMBOLS = {
    # 标准数集
    r'\mathbb{N}': '自然数集',
    r'\mathbb{Z}': '整数集',
    r'\mathbb{Q}': '有理数集',
    r'\mathbb{R}': '实数集',
    r'\mathbb{C}': '复数集',
}

# 常见错误符号及其推荐替代
COMMON_MATH_ERRORS = {
    # 符号错误
    r'(?<![a-zA-Z])N(?![a-zA-Z])': (r'\mathbb{N}', "标准数集应使用黑板体"),
    r'(?<![a-zA-Z])Z(?![a-zA-Z])': (r'\mathbb{Z}', "标准数集应使用黑板体"),
    r'(?<![a-zA-Z])Q(?![a-zA-Z])': (r'\mathbb{Q}', "标准数集应使用黑板体"),
    r'(?<![a-zA-Z])R(?![a-zA-Z])': (r'\mathbb{R}', "标准数集应使用黑板体"),
    r'(?<![a-zA-Z])C(?![a-zA-Z])': (r'\mathbb{C}', "标准数集应使用黑板体"),
}

# LaTeX 常见错误
LATEX_COMMON_ERRORS = {
    r'\\le\b': (r'\leq', '推荐使用 \\leq 代替 \\le'),
    r'\\ge\b': (r'\geq', '推荐使用 \\geq 代替 \\ge'),
    r'\\to\b(?!p)': (r'\rightarrow', '推荐使用 \\rightarrow 代替 \\to'),
    r'\\epsilon\b': (r'\varepsilon', '推荐使用 \\varepsilon 代替 \\epsilon'),
    r'\\phi\b(?!l)': (r'\varphi', '推荐使用 \\varphi 代替 \\phi'),
    r'\\theta\b': (r'\vartheta', '考虑使用 \\vartheta 代替 \\theta'),
}

# 函数名应使用正体
FUNCTION_NAMES = [
    'sin', 'cos', 'tan', 'cot', 'sec', 'csc',
    'arcsin', 'arccos', 'arctan',
    'sinh', 'cosh', 'tanh',
    'log', 'ln', 'lg', 'exp',
    'min', 'max', 'arg', 'gcd', 'lcm',
    'lim', 'sup', 'inf',
    'det', 'tr', 'rank',
    'deg', 'dim', 'ker', 'im',
]


class MathSymbolChecker:
    """数学符号检查器"""
    
    def __init__(self):
        self.issues: List[MathSymbolIssue] = []
        
    def check_file(self, file_path: Path) -> List[MathSymbolIssue]:
        """检查单个文件的数学符号"""
        issues = []
        content = file_path.read_text(encoding='utf-8')
        lines = content.split('\n')
        
        in_math_block = False
        math_block_start = 0
        
        for i, line in enumerate(lines, 1):
            # 检测数学块边界
            if line.strip().startswith('$$'):
                in_math_block = not in_math_block
                if in_math_block:
                    math_block_start = i
                continue
            
            # 检查行内和块级数学环境
            if '$' in line or in_math_block:
                # 1. 检查LaTeX常见错误
                issues.extend(self._check_latex_errors(file_path, i, line))
                
                # 2. 检查函数名格式
                issues.extend(self._check_function_names(file_path, i, line))
                
                # 3. 检查省略号使用
                issues.extend(self._check_ellipsis(file_path, i, line))
                
                # 4. 检查集合符号
                issues.extend(self._check_set_notation(file_path, i, line))
                
                # 5. 检查复杂度符号
                issues.extend(self._check_complexity_notation(file_path, i, line))
                
                # 6. 检查分数和对数
                issues.extend(self._check_fractions_and_logs(file_path, i, line))
        
        return issues
    
    def _check_latex_errors(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查LaTeX常见错误"""
        issues = []
        
        for pattern, (replacement, message) in LATEX_COMMON_ERRORS.items():
            if re.search(pattern, line):
                issues.append(MathSymbolIssue(
                    file=str(file_path),
                    line=line_num,
                    type='style',
                    severity='info',
                    message=message,
                    suggestion=f"替换为: {replacement}",
                    context=line[:80]
                ))
        
        return issues
    
    def _check_function_names(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查函数名是否使用正体"""
        issues = []
        
        # 只在数学环境中检查
        if '$' not in line:
            return issues
        
        for func in FUNCTION_NAMES:
            # 匹配 $...log...$ 中的log（斜体）
            pattern = rf'\$[^$]*\\?{func}\b[^$]*\$'
            for match in re.finditer(pattern, line, re.IGNORECASE):
                matched_text = match.group(0)
                # 检查是否已使用正体
                if rf'\{func}' not in matched_text and rf'\operatorname{{{func}}}' not in matched_text:
                    # 简单的启发式检查：如果函数名前后有数字或括号，可能是函数调用
                    if re.search(rf'\d.*{func}|{func}.*\(|\\{func}', matched_text):
                        issues.append(MathSymbolIssue(
                            file=str(file_path),
                            line=line_num,
                            type='symbol',
                            severity='info',
                            message=f'函数名 "{func}" 应使用正体 (\\{func} 或 \\operatorname{{{func}}})',
                            suggestion=f"使用: \\{func}",
                            context=line[:80]
                        ))
        
        return issues
    
    def _check_ellipsis(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查省略号使用"""
        issues = []
        
        if '$' in line:
            # 检查数学环境中的省略号
            math_segments = re.findall(r'\$([^$]+)\$', line)
            for segment in math_segments:
                if '...' in segment:
                    issues.append(MathSymbolIssue(
                        file=str(file_path),
                        line=line_num,
                        type='format',
                        severity='warning',
                        message='数学环境中应使用 \\cdots 或 \\ldots 代替 ...',
                        suggestion="使用: \\cdots (居中) 或 \\ldots (基线)",
                        context=line[:80]
                    ))
                elif ',' in segment and 'ldots' not in segment and 'cdots' not in segment:
                    # 检查逗号序列是否有省略号
                    if re.search(r',\s*,', segment) or re.search(r'a_\d+\s*,', segment):
                        # 可能是需要省略号的序列
                        pass
        
        return issues
    
    def _check_set_notation(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查集合符号使用"""
        issues = []
        
        if '$' in line:
            # 检查集合包含符号
            if re.search(r'[^\\]in\s', line) or re.search(r'\bin\b', line):
                # 检查是否使用了正确的属于符号
                pass  # 正常情况
            
            # 检查子集符号
            if re.search(r'subset\s+(?!eq)', line):
                # 使用了 \subset，可能需要 \subseteq
                pass
            
            # 检查空集符号
            if re.search(r'emptyset|empty', line, re.IGNORECASE):
                if 'emptyset' not in line and 'varnothing' not in line:
                    issues.append(MathSymbolIssue(
                        file=str(file_path),
                        line=line_num,
                        type='symbol',
                        severity='info',
                        message='空集应使用 \\emptyset 或 \\varnothing',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_complexity_notation(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查复杂度符号使用"""
        issues = []
        
        if '$' in line:
            # 检查 O(n) 格式
            if re.search(r'[^\\]O\([^)]+\)', line):
                # 使用了 O(而非\mathcal{O}或O)
                if '\mathcal{O}' not in line and 'O(' in line:
                    issues.append(MathSymbolIssue(
                        file=str(file_path),
                        line=line_num,
                        type='symbol',
                        severity='info',
                        message='大O符号可以使用 \\mathcal{{O}} 获得更好的排版效果',
                        suggestion=r"使用: $\mathcal{O}(n)$ 或 $O(n)$",
                        context=line[:80]
                    ))
            
            # 检查 Theta 和 Omega
            if re.search(r'\\Theta\b', line):
                # 正确使用了 \Theta
                pass
            if re.search(r'\\Omega\b', line):
                # 正确使用了 \Omega
                pass
        
        return issues
    
    def _check_fractions_and_logs(
        self, file_path: Path, line_num: int, line: str
    ) -> List[MathSymbolIssue]:
        """检查分数和对数格式"""
        issues = []
        
        if '$' in line:
            # 检查简单分数是否可以使用 \frac
            frac_pattern = r'\{[^}]+\}\s*/\s*\{[^}]+\}'
            if re.search(frac_pattern, line):
                # 在数学环境中使用斜杠表示分数
                issues.append(MathSymbolIssue(
                    file=str(file_path),
                    line=line_num,
                    type='format',
                    severity='info',
                    message='复杂分数建议使用 \\frac{{分子}}{{分母}}',
                    context=line[:80]
                ))
            
            # 检查对数底数
            if 'log' in line and 'log_' not in line:
                # 对数没有明确底数
                issues.append(MathSymbolIssue(
                    file=str(file_path),
                    line=line_num,
                    type='consistency',
                    severity='info',
                    message='对数函数建议明确底数 (\\log_2, \\ln, \\lg)',
                    suggestion="使用: \\log_2 n (算法), \\ln n (自然), \\lg n (常用)",
                    context=line[:80]
                ))
        
        return issues


def main():
    """主函数"""
    doc_path = Path('docs')
    
    if not doc_path.exists():
        print(f"❌ 错误: 文档目录不存在: {doc_path}")
        sys.exit(1)
    
    checker = MathSymbolChecker()
    all_issues = []
    checked_files = 0
    
    # 扫描所有Markdown文件
    for md_file in doc_path.rglob('*.md'):
        # 跳过特定文件
        if any(skip in str(md_file) for skip in ['README', '任务完成报告', '质量报告', '符号规范']):
            continue
        
        issues = checker.check_file(md_file)
        all_issues.extend(issues)
        if issues:
            checked_files += 1
    
    # 输出报告
    print("=" * 60)
    print("📐 数学符号检查报告 (ISO 80000-2)")
    print("=" * 60)
    print(f"检查文档数: {checked_files}")
    print(f"发现问题数: {len(all_issues)}")
    print()
    
    # 按严重程度统计
    severity_count = defaultdict(int)
    type_count = defaultdict(int)
    
    for issue in all_issues:
        severity_count[issue.severity] += 1
        type_count[issue.type] += 1
    
    print("按严重程度:")
    for sev, count in sorted(severity_count.items(), 
                              key=lambda x: {'error': 0, 'warning': 1, 'info': 2}[x[0]]):
        icon = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}[sev]
        print(f"  {icon} {sev}: {count}")
    
    print("\n按问题类型:")
    for typ, count in type_count.items():
        print(f"  - {typ}: {count}")
    
    print("\n" + "=" * 60)
    print("详细问题列表 (前20个):")
    print("=" * 60)
    
    for i, issue in enumerate(all_issues[:20], 1):
        icon = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}[issue.severity]
        print(f"\n{i}. {icon} [{issue.type}] {issue.file}:{issue.line}")
        print(f"   消息: {issue.message}")
        if issue.suggestion:
            print(f"   建议: {issue.suggestion}")
        if issue.context:
            print(f"   上下文: {issue.context[:60]}...")
    
    if len(all_issues) > 20:
        print(f"\n... 还有 {len(all_issues) - 20} 个问题未显示")
    
    # 输出ISO 80000-2合规建议
    print("\n" + "=" * 60)
    print("📖 ISO 80000-2 合规建议:")
    print("=" * 60)
    print("""
1. 标准数集使用黑板体: \\mathbb{{N}}, \\mathbb{{Z}}, \\mathbb{{Q}}, \\mathbb{{R}}, \\mathbb{{C}}
2. 变量使用斜体: $n$, $T(n)$, $f(x)$
3. 常数使用正体: \\mathrm{{e}}, \\pi, \\mathrm{{i}}
4. 函数名使用正体: \\log, \\sin, \\exp
5. 复杂度符号: \\mathcal{{O}}, \\Theta, \\Omega
6. 省略号: \\cdots (居中), \\ldots (基线对齐)
    """)
    
    # 返回退出码
    error_count = severity_count.get('error', 0)
    warning_count = severity_count.get('warning', 0)
    
    print("=" * 60)
    if error_count > 0:
        print(f"❌ 检查完成，发现 {error_count} 个错误")
        sys.exit(1)
    else:
        print(f"✅ 检查完成，发现 {warning_count} 个警告/建议")
        sys.exit(0)


if __name__ == '__main__':
    main()
