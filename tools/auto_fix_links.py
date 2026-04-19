#!/usr/bin/env python3
"""自动修复链接路径：尝试多种路径变体找到正确目标"""
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
    lines = content.split('\n')
    modified = False
    
    for i, line in enumerate(lines):
        for match in re.finditer(r'\[([^\]]+)\]\(([^)]+)\)', line):
            link_text = match.group(1)
            link_target = match.group(2)
            
            # Skip external, anchors, already correct
            if link_target.startswith(('http://', 'https://', '#')):
                continue
            if link_target in ('url', '文档路径', '路径', 'README.md'):
                continue
            if link_text in ('text', '术语', '文本', 'step.rule', 'int'):
                continue
            if '\\' in link_target:
                continue
            
            clean_target = link_target.split('#')[0]
            if not clean_target:
                continue
            
            # Check if current target exists
            target_path = md_file.parent / clean_target
            if target_path.exists() or target_path.with_suffix('.md').exists():
                continue
            
            # Try to find correct path by adjusting ../ count
            src_dir = md_file.parent
            rel_to_docs = src_dir.relative_to(docs_root)
            depth = len(rel_to_docs.parts)
            
            found = False
            # Try with different number of ../ prefixes
            for prefix in ['', './']:
                test = prefix + clean_target.lstrip('./')
                tp = src_dir / test
                if tp.exists() or tp.with_suffix('.md').exists():
                    if test != clean_target:
                        lines[i] = lines[i].replace(f']({link_target})', f']({link_target.replace(clean_target, test)})')
                        modified = True
                        found = True
                    break
            
            if found:
                continue
            
            # Try replacing ../../../ with ../../ etc.
            for extra_dots in range(1, 4):
                if clean_target.startswith('../' * extra_dots):
                    reduced = clean_target[3*extra_dots:]
                    for prefix in ['../' * (extra_dots - 1), './', '']:
                        test = prefix + reduced
                        tp = src_dir / test
                        if tp.exists() or tp.with_suffix('.md').exists():
                            # Reconstruct full target with anchor
                            anchor = ''
                            if '#' in link_target:
                                anchor = '#' + link_target.split('#', 1)[1]
                            new_target = test + anchor
                            lines[i] = lines[i].replace(f']({link_target})', f']({new_target})')
                            modified = True
                            found = True
                            break
                    if found:
                        break
            
            if found:
                continue
            
            # Try adding ../ prefix
            for add_dots in range(1, 4):
                test = '../' * add_dots + clean_target.lstrip('./')
                tp = src_dir / test
                if tp.exists() or tp.with_suffix('.md').exists():
                    anchor = ''
                    if '#' in link_target:
                        anchor = '#' + link_target.split('#', 1)[1]
                    new_target = test + anchor
                    lines[i] = lines[i].replace(f']({link_target})', f']({new_target})')
                    modified = True
                    found = True
                    break
    
    if modified:
        md_file.write_text('\n'.join(lines), encoding='utf-8')
        fixed_count += 1

print(f'Fixed links in {fixed_count} files')
