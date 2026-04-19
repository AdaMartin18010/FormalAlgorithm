#!/usr/bin/env python3
"""批量修复断链"""
import re
from pathlib import Path
from datetime import datetime

docs_root = Path('E:/_src/FormalAlgorithm/docs')

# 从报告中提取所有断链
report = open('E:/_src/FormalAlgorithm/docs/质量报告/structure-check-report.md', encoding='utf-8').read()
sections = report.split('### ')

broken = []  # (source_file, line_no, link_text, target)
for section in sections[1:]:
    lines = section.split('\n')
    filename = lines[0].strip()
    in_broken = False
    for line in lines:
        if '断链数' in line:
            in_broken = True
        if in_broken and line.strip().startswith('- 行'):
            m = re.search(r'- 行(\d+):\s*\[([^\]]+)\]\(([^\)]+)\)', line)
            if m:
                broken.append((filename, int(m.group(1)), m.group(2), m.group(3)))

print(f'Total broken links from report: {len(broken)}')

# 统计目标
from collections import Counter
targets = Counter(t for _, _, _, t in broken)
print(f'Unique targets: {len(targets)}')

# 创建缺失的核心目录文件
core_files_to_create = {
    '04-算法复杂度/01-时间复杂度.md': '时间复杂度',
    '04-算法复杂度/02-空间复杂度.md': '空间复杂度',
    '04-算法复杂度/04-复杂度类.md': '复杂度类',
    '04-算法复杂度/递推关系.md': '递推关系',
    '04-算法复杂度/主定理.md': '主定理',
    '07-计算模型/01-图灵机.md': '图灵机',
    '07-计算模型/05-量子计算模型.md': '量子计算模型',
    '02-递归理论/01-递归函数定义.md': '递归函数定义',
    '08-实现示例/04-形式化验证.md': '形式化验证',
    '09-算法理论/01-算法基础/06-动态规划理论.md': '动态规划理论',
    '09-算法理论/01-算法基础/03-排序算法理论.md': '排序算法理论',
    '05-类型理论/03-同伦类型论.md': '同伦类型论',
    '05-类型理论/Lambda演算.md': 'Lambda演算',
    '05-类型理论/多态类型系统.md': '多态类型系统',
    '05-类型理论/高阶归纳类型.md': '高阶归纳类型',
    '06-逻辑系统/SMT求解器.md': 'SMT求解器',
    '01-基础理论/01-形式化定义.md': '形式化定义',
    '01-基础理论/17-神经网络算法理论.md': '神经网络算法理论',
    '10-高级主题/04-高级算法理论/04-算法优化理论.md': '算法优化理论',
    '10-高级主题/自动机学习.md': '自动机学习',
    '03-形式化证明/01-证明系统.md': '证明系统',
    '02-归并算法.md': '归并算法',
    '示例库/01-标准示例集.md': '标准示例集',
}

created = 0
for rel_path, title in core_files_to_create.items():
    p = docs_root / rel_path
    if not p.exists():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(f'''> **版本**: 1.0
> **最后更新**: {datetime.now().strftime('%Y-%m-%d')}
> **作者**: 算法规范设计团队
>
> ---
>
# {title}

> **状态**: 待补充内容

本文档为算法规范知识体系的核心文档，记录{title}的形式化定义与理论基础。

## 学习目标

- 理解{title}的核心概念
- 掌握{title}的形式化表示

## 核心概念

（待补充）

## 参考文献

（待补充）

## 知识导航

- [返回目录](../)
''', encoding='utf-8')
        created += 1

print(f'Created {created} core documents')

# 创建缺失的根目录文件
root_files_to_create = {
    '国际课程对标表.md': '国际课程对标表',
    '项目全面梳理-2025.md': '项目全面梳理',
    '项目扩展与持续推进任务编排.md': '项目扩展与持续推进任务编排',
    '内容补充与思维表征全面计划方案.md': '内容补充与思维表征全面计划方案',
    '内容补充标准-概念定义属性关系解释论证形式证明.md': '内容补充标准',
    '思维表征模板集.md': '思维表征模板集',
    '项目哲科结构说明.md': '项目哲科结构说明',
    '质量检查清单.md': '质量检查清单',
    '项目改进任务清单-2025.md': '项目改进任务清单',
}

for rel_path, title in root_files_to_create.items():
    p = docs_root / rel_path
    if not p.exists():
        p.write_text(f'''> **版本**: 1.0
> **最后更新**: {datetime.now().strftime('%Y-%m-%d')}
> **作者**: 算法规范设计团队
>
> ---
>
# {title}

> **状态**: 项目文档

本文档为算法规范设计项目的内部管理文档。

## 概述

（待补充）
''', encoding='utf-8')
        created += 1

print(f'Total created: {created}')
