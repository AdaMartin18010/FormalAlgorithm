#!/usr/bin/env python3
"""
质量检查集成工具
运行所有质量检查并生成报告
"""

import subprocess
import sys
from datetime import datetime
from pathlib import Path

def run_checker(script_name: str) -> tuple:
    """运行单个检查脚本"""
    try:
        result = subprocess.run(
            [sys.executable, f'tools/{script_name}'],
            capture_output=True,
            text=True,
            timeout=120,
            encoding='utf-8'
        )
        return result.stdout, result.returncode
    except Exception as e:
        return f"Error running {script_name}: {e}", 1

def main():
    """主函数"""
    print("=" * 70)
    print("综合质量检查")
    print("=" * 70)
    print()
    
    checkers = [
        ('citation_checker.py', '引用检查'),
        ('math_symbol_checker.py', '数学符号检查'),
        ('doc_structure_checker.py', '文档结构检查'),
    ]
    
    all_outputs = []
    
    for script, name in checkers:
        print(f"\n运行 {name}...")
        print("-" * 70)
        output, returncode = run_checker(script)
        print(output)
        all_outputs.append((name, output, returncode))
    
    # 生成综合报告
    report_lines = [
        "# 综合质量检查报告",
        "",
        f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        "## 执行摘要",
        "",
    ]
    
    for name, output, returncode in all_outputs:
        status = "✅ 通过" if returncode == 0 else "⚠️ 有警告"
        report_lines.append(f"- {name}: {status}")
    
    report_lines.extend([
        "",
        "## 详细输出",
        "",
    ])
    
    for name, output, returncode in all_outputs:
        report_lines.append(f"### {name}")
        report_lines.append("```")
        report_lines.append(output)
        report_lines.append("```")
        report_lines.append("")
    
    report_lines.extend([
        "## 建议行动",
        "",
        "1. 查看各专项报告了解详细问题",
        "2. 优先处理标记为'错误'的问题",
        "3. 考虑标记为'风格'和'建议'的改进",
        "4. 定期运行此检查以维持质量",
        "",
    ])
    
    report_path = Path('docs/质量报告/quality-check-report.md')
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text('\n'.join(report_lines), encoding='utf-8')
    
    print("\n" + "=" * 70)
    print(f"综合报告已保存: {report_path}")
    print("=" * 70)

if __name__ == '__main__':
    main()
