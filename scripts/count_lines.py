#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
统计项目代码行数脚本

功能：
- 统计项目中各种类型文件的行数
- 支持排除特定目录和文件
- 生成详细的统计报告

使用方法：
    python count_lines.py [options]

选项：
    --path, -p      要统计的路径（默认: 项目根目录）
    --output, -o    输出文件路径（可选）
    --format, -f    输出格式: text, json, csv（默认: text）
    --help, -h      显示帮助信息
"""

import os
import json
import csv
import argparse
from pathlib import Path
from collections import defaultdict, Counter
from datetime import datetime


# 默认排除的目录
DEFAULT_EXCLUDE_DIRS = {
    '.git', '.github', '.vscode', 'node_modules', '__pycache__',
    'venv', '.venv', 'env', '.env', 'dist', 'build', 'target',
    '.idea', '.vs', 'bin', 'obj', 'out', 'release', 'Release'
}

# 默认排除的文件
DEFAULT_EXCLUDE_FILES = {
    '.gitignore', '.gitattributes', '.DS_Store', 'Thumbs.db',
    'package-lock.json', 'yarn.lock', 'Cargo.lock', 'poetry.lock',
    'Pipfile.lock', 'Gemfile.lock'
}

# 文件类型映射
FILE_TYPE_MAP = {
    # 代码文件
    '.py': 'Python',
    '.js': 'JavaScript',
    '.ts': 'TypeScript',
    '.jsx': 'React',
    '.tsx': 'React TS',
    '.java': 'Java',
    '.c': 'C',
    '.cpp': 'C++',
    '.cc': 'C++',
    '.cxx': 'C++',
    '.h': 'C/C++ Header',
    '.hpp': 'C++ Header',
    '.cs': 'C#',
    '.go': 'Go',
    '.rs': 'Rust',
    '.rb': 'Ruby',
    '.php': 'PHP',
    '.swift': 'Swift',
    '.kt': 'Kotlin',
    '.scala': 'Scala',
    '.r': 'R',
    '.m': 'Objective-C',
    '.mm': 'Objective-C++',
    '.lua': 'Lua',
    '.sh': 'Shell',
    '.bash': 'Bash',
    '.zsh': 'Zsh',
    '.ps1': 'PowerShell',
    '.pl': 'Perl',
    '.pm': 'Perl',
    '.t': 'Perl',
    
    # 标记语言
    '.md': 'Markdown',
    '.markdown': 'Markdown',
    '.rst': 'reStructuredText',
    '.tex': 'LaTeX',
    '.html': 'HTML',
    '.htm': 'HTML',
    '.xml': 'XML',
    '.yaml': 'YAML',
    '.yml': 'YAML',
    '.toml': 'TOML',
    '.ini': 'INI',
    '.cfg': 'Config',
    '.conf': 'Config',
    
    # 样式文件
    '.css': 'CSS',
    '.scss': 'SCSS',
    '.sass': 'Sass',
    '.less': 'Less',
    
    # 数据文件
    '.json': 'JSON',
    '.csv': 'CSV',
    '.sql': 'SQL',
    
    # 其他
    '.dockerfile': 'Dockerfile',
    'dockerfile': 'Dockerfile',
    '.makefile': 'Makefile',
    'makefile': 'Makefile',
    '.cmake': 'CMake',
    '.gradle': 'Gradle',
    '.sbt': 'SBT',
}


def get_file_type(file_path):
    """获取文件类型"""
    name_lower = file_path.name.lower()
    
    # 检查特殊文件名
    if name_lower in FILE_TYPE_MAP:
        return FILE_TYPE_MAP[name_lower]
    
    # 检查扩展名
    suffix = file_path.suffix.lower()
    if suffix in FILE_TYPE_MAP:
        return FILE_TYPE_MAP[suffix]
    
    return 'Other'


def count_lines_in_file(file_path):
    """统计单个文件的行数"""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
            total = len(lines)
            code = len([l for l in lines if l.strip()])
            blank = total - code
            return total, code, blank
    except Exception as e:
        return 0, 0, 0


def should_exclude(path, exclude_dirs, exclude_files, exclude_patterns):
    """检查是否应该排除该路径"""
    name = path.name
    
    if path.is_dir():
        if name in exclude_dirs:
            return True
    else:
        if name in exclude_files:
            return True
        for pattern in exclude_patterns:
            if path.match(pattern):
                return True
    
    return False


def scan_directory(directory, exclude_dirs, exclude_files, exclude_patterns):
    """扫描目录，返回文件统计信息"""
    stats = defaultdict(lambda: {'files': 0, 'total': 0, 'code': 0, 'blank': 0})
    file_details = []
    
    for root, dirs, files in os.walk(directory):
        root_path = Path(root)
        
        # 过滤目录
        dirs[:] = [d for d in dirs if not should_exclude(
            root_path / d, exclude_dirs, exclude_files, exclude_patterns
        )]
        
        for filename in files:
            file_path = root_path / filename
            
            if should_exclude(file_path, exclude_dirs, exclude_files, exclude_patterns):
                continue
            
            file_type = get_file_type(file_path)
            total, code, blank = count_lines_in_file(file_path)
            
            if total > 0:
                stats[file_type]['files'] += 1
                stats[file_type]['total'] += total
                stats[file_type]['code'] += code
                stats[file_type]['blank'] += blank
                
                file_details.append({
                    'path': str(file_path.relative_to(directory)),
                    'type': file_type,
                    'total': total,
                    'code': code,
                    'blank': blank
                })
    
    return stats, file_details


def format_text_report(stats, total_files, project_name):
    """格式化文本报告"""
    lines = [
        f"# {project_name} 代码统计报告",
        "",
        f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        "## 概览",
        "",
        f"总文件数: {total_files}",
        "",
        "## 按语言统计",
        "",
        "| 语言 | 文件数 | 总行数 | 代码行 | 空行 | 代码比例 |",
        "|------|--------|--------|--------|------|----------|",
    ]
    
    # 按总行数排序
    sorted_stats = sorted(stats.items(), key=lambda x: x[1]['total'], reverse=True)
    
    grand_total = sum(s['total'] for s in stats.values())
    grand_code = sum(s['code'] for s in stats.values())
    grand_blank = sum(s['blank'] for s in stats.values())
    
    for lang, data in sorted_stats:
        ratio = (data['code'] / data['total'] * 100) if data['total'] > 0 else 0
        lines.append(
            f"| {lang} | {data['files']} | {data['total']:,} | "
            f"{data['code']:,} | {data['blank']:,} | {ratio:.1f}% |"
        )
    
    lines.append(
        f"| **总计** | **{total_files}** | **{grand_total:,}** | "
        f"**{grand_code:,}** | **{grand_blank:,}** | "
        f"**{(grand_code/grand_total*100 if grand_total > 0 else 0):.1f}%** |"
    )
    
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append(f"*由 scripts/count_lines.py 生成*")
    
    return '\n'.join(lines)


def format_json_report(stats, file_details, total_files, project_name):
    """格式化 JSON 报告"""
    return json.dumps({
        'project': project_name,
        'generated_at': datetime.now().isoformat(),
        'summary': {
            'total_files': total_files,
            'total_lines': sum(s['total'] for s in stats.values()),
            'code_lines': sum(s['code'] for s in stats.values()),
            'blank_lines': sum(s['blank'] for s in stats.values()),
        },
        'by_language': dict(stats),
        'files': file_details
    }, indent=2, ensure_ascii=False)


def format_csv_report(file_details):
    """格式化 CSV 报告"""
    output = []
    writer = csv.writer(output)
    writer.writerow(['Path', 'Type', 'Total Lines', 'Code Lines', 'Blank Lines'])
    
    for file in file_details:
        writer.writerow([
            file['path'],
            file['type'],
            file['total'],
            file['code'],
            file['blank']
        ])
    
    return '\n'.join(output)


def main():
    parser = argparse.ArgumentParser(
        description='统计项目代码行数',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python count_lines.py
  python count_lines.py -p src -o stats.md
  python count_lines.py -f json -o stats.json
  python count_lines.py --exclude-dir node_modules dist
        """
    )
    parser.add_argument(
        '--path', '-p',
        default='.',
        help='要统计的路径 (默认: 当前目录)'
    )
    parser.add_argument(
        '--output', '-o',
        help='输出文件路径'
    )
    parser.add_argument(
        '--format', '-f',
        choices=['text', 'json', 'csv'],
        default='text',
        help='输出格式 (默认: text)'
    )
    parser.add_argument(
        '--exclude-dir',
        nargs='+',
        default=[],
        help='额外排除的目录'
    )
    parser.add_argument(
        '--exclude-file',
        nargs='+',
        default=[],
        help='额外排除的文件'
    )
    parser.add_argument(
        '--exclude-pattern',
        nargs='+',
        default=[],
        help='排除模式 (如: *.min.js)'
    )
    
    args = parser.parse_args()
    
    # 确定项目根目录
    script_dir = Path(__file__).parent.resolve()
    project_root = script_dir.parent
    
    # 确定要扫描的路径
    if args.path == '.':
        scan_path = project_root
    else:
        scan_path = Path(args.path).resolve()
    
    project_name = project_root.name
    
    # 合并排除项
    exclude_dirs = DEFAULT_EXCLUDE_DIRS | set(args.exclude_dir)
    exclude_files = DEFAULT_EXCLUDE_FILES | set(args.exclude_file)
    exclude_patterns = set(args.exclude_pattern)
    
    print(f"正在扫描: {scan_path}")
    print("请稍候...")
    
    # 扫描目录
    stats, file_details = scan_directory(scan_path, exclude_dirs, exclude_files, exclude_patterns)
    total_files = sum(s['files'] for s in stats.values())
    
    print(f"扫描完成: 找到 {total_files} 个文件")
    
    # 生成报告
    if args.format == 'json':
        report = format_json_report(stats, file_details, total_files, project_name)
    elif args.format == 'csv':
        report = format_csv_report(file_details)
    else:
        report = format_text_report(stats, total_files, project_name)
    
    # 输出报告
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"报告已保存: {output_path}")
    else:
        print()
        print(report)


if __name__ == '__main__':
    main()
