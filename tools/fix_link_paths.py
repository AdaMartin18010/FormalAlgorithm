#!/usr/bin/env python3
"""批量修复链接路径错误"""
import re
from pathlib import Path

docs_root = Path('E:/_src/FormalAlgorithm/docs')
fixed_count = 0

for md_file in docs_root.rglob('*.md'):
    try:
        content = md_file.read_text(encoding='utf-8')
    except:
        continue
    
    original = content
    rel_parts = md_file.relative_to(docs_root).parts
    is_root_doc = len(rel_parts) == 1  # docs/xxx.md
    
    # Fix 1: Root docs using ../XX- to point to sibling dirs (should be ./XX-)
    if is_root_doc:
        for i in range(1, 13):
            dir_prefix = f'../{i:02d}-'
            correct_prefix = f'./{i:02d}-'
            content = content.replace(f']({dir_prefix}', f']({correct_prefix}')
            content = content.replace(f'](../../{i:02d}-', f'](..../../{i:02d}-')  # don't touch these in root
    
    # Fix 2: Deep docs using ../../../ for root-level files (should be ../../)
    # Only for files that are 2+ levels deep in docs/
    if len(rel_parts) >= 3:
        # Files in docs/X/Y/... using ../../../xxx.md should use ../../xxx.md
        for target in ['项目全面梳理-2025.md', '项目扩展与持续推进任务编排.md', 
                       '国际课程对标表.md', '内容补充与思维表征全面计划方案.md',
                       '内容补充标准-概念定义属性关系解释论证形式证明.md', '思维表征模板集.md',
                       '项目哲科结构说明.md', '质量检查清单.md', '项目改进任务清单-2025.md']:
            content = content.replace(f'../../../{target}', f'../../{target}')
    
    # Fix 3: Broken link [证明助手](知识笔记/证明助手(Coq-Lean-Agda)
    # This is likely a malformed link, find the actual file
    if '证明助手(Coq-Lean-Agda' in content:
        content = content.replace(
            '[证明助手](知识笔记/证明助手(Coq-Lean-Agda',
            '[证明助手](知识笔记/证明助手.md'
        )
    
    if content != original:
        md_file.write_text(content, encoding='utf-8')
        fixed_count += 1

print(f'Fixed {fixed_count} files')
