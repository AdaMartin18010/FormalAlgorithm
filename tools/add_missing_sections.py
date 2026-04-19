#!/usr/bin/env python3
"""为核心目录文件批量添加缺少的标准章节"""
import re
from pathlib import Path
from datetime import datetime

docs_root = Path('E:/_src/FormalAlgorithm/docs')
core_dirs = [f'{i:02d}-' for i in range(13)]

REQUIRED_SECTIONS = ['## 学习目标', '## 参考文献', '## 知识导航']

fixed = 0
for md_file in docs_root.rglob('*.md'):
    # Only process core dirs
    rel = str(md_file.relative_to(docs_root))
    if not any(rel.startswith(d) for d in core_dirs):
        continue
    
    try:
        content = md_file.read_text(encoding='utf-8')
    except:
        continue
    
    missing = [s for s in REQUIRED_SECTIONS if s not in content]
    if not missing:
        continue
    
    # Extract title from first heading
    title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    title = title_match.group(1) if title_match else md_file.stem
    
    # Build sections to add
    sections_to_add = []
    if '## 学习目标' in missing:
        sections_to_add.append(f"""## 学习目标

- 理解{title}的核心概念
- 掌握{title}的形式化表示
""")
    if '## 参考文献' in missing:
        sections_to_add.append("""## 参考文献

（待补充）
""")
    if '## 知识导航' in missing:
        sections_to_add.append("""## 知识导航

- [返回目录](../)
""")
    
    # Append at the end
    new_content = content.rstrip() + '\n\n' + '\n'.join(sections_to_add)
    md_file.write_text(new_content, encoding='utf-8')
    fixed += 1

print(f'Added missing sections to {fixed} core documents')
