#!/usr/bin/env python3
"""精确修复剩余断链"""
import re
from pathlib import Path

docs_root = Path('E:/_src/FormalAlgorithm/docs')

# 1. Fix video course script links (..../ -> ../)
for md in (docs_root / '视频课程脚本').rglob('*.md'):
    try:
        content = md.read_text(encoding='utf-8')
    except: continue
    content = content.replace('..../04-算法复杂度/', '../04-算法复杂度/')
    content = content.replace('..../09-算法理论/', '../09-算法理论/')
    md.write_text(content, encoding='utf-8')
    print(f'Fixed video links in {md.name}')

# 2. Fix 项目维护/内容复用指南.md links
reuse_guide = docs_root / '项目维护' / '内容复用指南.md'
if reuse_guide.exists():
    content = reuse_guide.read_text(encoding='utf-8')
    content = content.replace('[图灵机](./01-图灵机.md)', '[图灵机](../知识笔记/01-图灵机.md)')
    content = content.replace('[贪心算法](./07-贪心算法理论.md)', '[贪心算法](../知识笔记/07-贪心算法理论.md)')
    content = content.replace('[依赖类型论](../02-依赖类型论.md)', '[依赖类型论](../05-类型理论/02-依赖类型论.md)')
    reuse_guide.write_text(content, encoding='utf-8')
    print('Fixed 内容复用指南.md')

# 3. Fix 可视化/知识图谱可视化.md
kg_vis = docs_root / '可视化' / '知识图谱可视化.md'
if kg_vis.exists():
    content = kg_vis.read_text(encoding='utf-8')
    content = content.replace('[算法设计模式关系图](算法设计模式关系图.md)', '[算法设计模式关系图](../知识笔记/算法设计模式关系图.md)')
    kg_vis.write_text(content, encoding='utf-8')
    print('Fixed 知识图谱可视化.md')

# 4. Fix 09-算法理论 links
fixes = {
    '09-算法理论/01-算法基础/13-在线算法理论-扩展.md': {
        '[多臂老虎机算法](./多臂老虎机算法.md)': '[多臂老虎机算法](../知识笔记/多臂老虎机算法.md)',
        '[博弈论算法](./博弈论算法.md)': '[博弈论算法](../知识笔记/博弈论算法.md)',
    },
    '09-算法理论/01-算法基础/字符串算法理论.md': {
        '[KMP算法](./KMP字符串匹配.md)': '[KMP算法](../知识笔记/KMP字符串匹配.md)',
    },
    '09-算法理论/02-复杂度理论/交互式证明系统.md': {
        '[零知识证明](../10-高级主题/零知识证明.md)': '[零知识证明](../../10-高级主题/零知识证明.md)',
        '[量子计算复杂性](../05-量子类型系统.md)': '[量子计算复杂性](../../05-量子类型系统.md)',
    },
    '09-算法理论/03-优化理论/乘性权重算法.md': {
        '[博弈论算法](./博弈论算法.md)': '[博弈论算法](../知识笔记/博弈论算法.md)',
    },
    '09-算法理论/04-高级算法理论/计算几何理论.md': {
        '[范围搜索](./范围搜索与k-d树.md)': '[范围搜索](../知识笔记/范围搜索与k-d树.md)',
        '[Voronoi图](./Voronoi图.md)': '[Voronoi图](../知识笔记/Voronoi图.md)',
    },
}

for rel_path, replacements in fixes.items():
    p = docs_root / rel_path
    if p.exists():
        content = p.read_text(encoding='utf-8')
        for old, new in replacements.items():
            content = content.replace(old, new)
        p.write_text(content, encoding='utf-8')
        print(f'Fixed {rel_path}')

# 5. Enhance checker: filter string key
print('Done')
