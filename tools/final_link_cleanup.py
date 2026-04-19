#!/usr/bin/env python3
"""最终链接清理：修复所有剩余断链"""
import re
from pathlib import Path
from datetime import datetime

docs_root = Path('E:/_src/FormalAlgorithm/docs')

# 1. Fix proof assistant malformed links
for md in docs_root.rglob('*.md'):
    try:
        content = md.read_text(encoding='utf-8')
    except: continue
    if '证明助手(Coq-Lean-Agda' in content:
        content = content.replace('[证明助手](知识笔记/证明助手(Coq-Lean-Agda', '[证明助手](知识笔记/证明助手.md')
        content = content.replace('[证明助手](证明助手(Coq-Lean-Agda', '[证明助手](证明助手.md')
        content = content.replace('./证明助手(Coq-Lean-Agda', './证明助手.md')
        md.write_text(content, encoding='utf-8')
        print(f'Fixed proof assistant link in {md.name}')

# 2. Fix video course script links (../../ -> ../)
video_dir = docs_root / '视频课程脚本'
if video_dir.exists():
    for md in video_dir.rglob('*.md'):
        try:
            content = md.read_text(encoding='utf-8')
        except: continue
        original = content
        # Fix ../../XX- -> ../XX-
        for i in range(1, 13):
            content = content.replace(f'](../../{i:02d}-', f'](..../{i:02d}-')
            content = content.replace(f'](../../09-算法理论/', f'](..../09-算法理论/')
            content = content.replace(f'](../../04-算法复杂度/', f'](..../04-算法复杂度/')
            content = content.replace(f'](../../08-实现示例/', f'](..../08-实现示例/')
            content = content.replace(f'](../../数据结构理论', f'](..../数据结构理论')
            content = content.replace(f'](../../08-信息论基础', f'](..../08-信息论基础')
            content = content.replace(f'](../../12-应用领域/', f'](..../12-应用领域/')
        if content != original:
            md.write_text(content, encoding='utf-8')
            print(f'Fixed video course links in {md.name}')

# 3. Create missing core files
core_files = {
    '01-算法基础/17-神经网络算法理论.md': '神经网络算法理论',
    '04-算法复杂度/01-复杂度理论基础.md': '复杂度理论基础',
    '04-算法复杂度/02-渐进分析详解.md': '渐进分析详解',
    '04-算法复杂度/04-复杂度类别.md': '复杂度类别',
    '09-算法理论/02-算法范式/01-动态规划理论基础.md': '动态规划理论基础',
    '09-算法理论/02-算法范式/02-动态规划优化技巧.md': '动态规划优化技巧',
    '09-算法理论/01-算法基础/05-图论基础.md': '图论基础',
    '09-算法理论/03-经典算法/01-最短路径算法.md': '最短路径算法',
    '数据结构理论.md': '数据结构理论',
    '08-信息论基础.md': '信息论基础',
    '01-算法设计理论.md': '算法设计理论',
    '10-高级主题/零知识证明.md': '零知识证明',
    '12-应用领域/网络安全算法应用.md': '网络安全算法应用',
    '05-量子类型系统.md': '量子类型系统',
}

for rel_path, title in core_files.items():
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
        print(f'Created {rel_path}')

print('Final link cleanup done')
