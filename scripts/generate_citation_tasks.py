#!/usr/bin/env python3
"""
引用修复任务清单生成脚本
扫描 docs/ 目录下所有 .md 文件，查找"待补充"占位符
输出按优先级排序的 Markdown 任务清单
"""

import re
import sys
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# 优先级规则映射
PRIORITY_RULES = [
    ('P0', ['01-基础理论', '02-递归理论', '03-形式化证明', '13-LeetCode']),
    ('P1', ['04-算法复杂度', '05-类型理论', '06-逻辑系统', '07-计算模型']),
    ('P2', ['09-算法理论', '10-高级主题', '12-应用领域']),
]

# 默认优先级为 P2（其他所有未匹配的模块）
DEFAULT_PRIORITY = 'P2'


def get_priority(relative_path: str) -> str:
    """根据文件路径判断优先级"""
    for priority, prefixes in PRIORITY_RULES:
        for prefix in prefixes:
            if prefix in relative_path:
                return priority
    return DEFAULT_PRIORITY


def scan_docs(docs_path: Path) -> tuple:
    """
    扫描 docs 目录，返回:
      - 文件列表（每个元素为 dict）
      - 模块统计 dict
    """
    results = []
    module_stats = defaultdict(int)  # 按模块统计待补充总数
    total_files = 0
    total_placeholders = 0

    for md_file in sorted(docs_path.rglob('*.md')):
        content = md_file.read_text(encoding='utf-8')
        count = len(re.findall(r'待补充', content))
        if count == 0:
            continue

        rel_path = md_file.relative_to(docs_path).as_posix()
        priority = get_priority(rel_path)
        # 模块取第一级目录名
        module = rel_path.split('/')[0] if '/' in rel_path else '其他'

        results.append({
            'path': rel_path,
            'count': count,
            'module': module,
            'priority': priority,
        })
        module_stats[module] += count
        total_files += 1
        total_placeholders += count

    return results, module_stats, total_files, total_placeholders


def generate_markdown(results, module_stats, total_files, total_placeholders) -> str:
    """生成 Markdown 格式的任务清单"""
    lines = []
    today = datetime.now().strftime('%Y-%m-%d')

    lines.append('# 引用修复任务清单')
    lines.append('')
    lines.append(f'> **生成日期**: {today}')
    lines.append(f'> **扫描范围**: `docs/` 目录下所有 Markdown 文件')
    lines.append(f'> **统计**: {total_files} 个文件含有待补充占位符，共计 {total_placeholders} 处')
    lines.append('')
    lines.append('---')
    lines.append('')

    # 按优先级分组
    priority_order = {'P0': 0, 'P1': 1, 'P2': 2}
    results.sort(key=lambda x: (priority_order[x['priority']], -x['count']))

    for priority in ['P0', 'P1', 'P2']:
        group = [r for r in results if r['priority'] == priority]
        if not group:
            continue

        lines.append(f'## {priority} 优先级')
        lines.append('')
        if priority == 'P0':
            lines.append('核心模块（基础理论、递归理论、形式化证明、LeetCode），引用修复优先级最高。')
        elif priority == 'P1':
            lines.append('重要模块（算法复杂度、类型理论、逻辑系统、计算模型），引用修复优先级次高。')
        else:
            lines.append('扩展模块（算法理论、高级主题、应用领域及其他），引用修复优先级较低。')
        lines.append('')
        lines.append('| 序号 | 文件路径 | 待补充次数 | 所属模块 | 状态 |')
        lines.append('|:----:|----------|:----------:|----------|:----:|')

        for idx, item in enumerate(group, 1):
            # 默认状态为 ⏳ 待修复
            lines.append(
                f'| {idx} | `{item["path"]}` | {item["count"]} | {item["module"]} | ⏳ 待修复 |'
            )
        lines.append('')

    # 模块统计
    lines.append('---')
    lines.append('')
    lines.append('## 按模块统计')
    lines.append('')
    lines.append('| 模块 | 待补充引用数量 |')
    lines.append('|------|:------------:|')
    for mod, cnt in sorted(module_stats.items(), key=lambda x: -x[1]):
        lines.append(f'| {mod} | {cnt} |')
    lines.append('')
    lines.append(f'| **合计** | **{total_placeholders}** |')
    lines.append('')

    # 使用说明
    lines.append('---')
    lines.append('')
    lines.append('## 使用说明')
    lines.append('')
    lines.append('1. 运行本脚本自动生成最新清单：')
    lines.append('   ```bash')
    lines.append('   python scripts/generate_citation_tasks.py')
    lines.append('   ```')
    lines.append('2. 自动修复优先级高的文件时，请先备份原文件到 `.backup/` 目录。')
    lines.append('3. 每修复完一个文件，请在对应行的"状态"列标记为 `✅ 已完成`。')
    lines.append('4. 对于无法确定具体引用位置的文件，保留在清单中并标注 `❓ 需人工复核`。')
    lines.append('')

    return '\n'.join(lines)


def main():
    docs_path = Path('docs')
    if not docs_path.exists():
        print(f'错误: {docs_path} 目录不存在', file=sys.stderr)
        sys.exit(1)

    results, module_stats, total_files, total_placeholders = scan_docs(docs_path)
    markdown = generate_markdown(results, module_stats, total_files, total_placeholders)

    output_path = Path('docs/项目维护/引用修复任务清单_{}.md'.format(
        datetime.now().strftime('%Y-%m-%d')
    ))
    output_path.write_text(markdown, encoding='utf-8')
    print(f'任务清单已生成: {output_path}')
    print(f'统计: {total_files} 个文件, {total_placeholders} 处待补充')


if __name__ == '__main__':
    main()
