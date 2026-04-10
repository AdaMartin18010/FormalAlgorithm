#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
自动生成文档索引脚本

功能：
- 扫描 docs/ 目录下的所有 Markdown 文件
- 生成文档索引（README.md）
- 支持按目录分组和排序

使用方法：
    python generate_index.py [options]

选项：
    --output, -o    输出文件路径（默认: docs/README.md）
    --verbose, -v   显示详细信息
    --help, -h      显示帮助信息
"""

import os
import re
import argparse
from pathlib import Path
from datetime import datetime
from collections import defaultdict


def extract_title(file_path):
    """从 Markdown 文件中提取标题"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            # 查找第一个 # 开头的标题
            match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
            if match:
                return match.group(1).strip()
    except Exception as e:
        pass
    # 如果无法提取标题，使用文件名
    return Path(file_path).stem


def extract_description(file_path):
    """从 Markdown 文件中提取描述（第一个非空段落）"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            # 移除代码块
            content = re.sub(r'```[\s\S]*?```', '', content)
            # 查找第一个非空段落
            paragraphs = content.split('\n\n')
            for para in paragraphs:
                para = para.strip()
                if para and not para.startswith('#') and not para.startswith('<'):
                    # 限制描述长度
                    desc = para.replace('\n', ' ')
                    if len(desc) > 150:
                        desc = desc[:147] + '...'
                    return desc
    except Exception as e:
        pass
    return ''


def scan_docs(docs_dir):
    """扫描文档目录，返回文件信息列表"""
    docs_dir = Path(docs_dir)
    files = []
    
    if not docs_dir.exists():
        print(f"错误: 目录不存在 {docs_dir}")
        return files
    
    for md_file in docs_dir.rglob('*.md'):
        # 跳过 README.md 和索引文件
        if md_file.name == 'README.md' and md_file.parent == docs_dir:
            continue
        if '索引' in md_file.name or 'index' in md_file.name.lower():
            continue
            
        rel_path = md_file.relative_to(docs_dir)
        title = extract_title(md_file)
        description = extract_description(md_file)
        
        files.append({
            'path': rel_path,
            'title': title,
            'description': description,
            'category': rel_path.parts[0] if len(rel_path.parts) > 1 else '其他'
        })
    
    return sorted(files, key=lambda x: str(x['path']))


def generate_index(files, project_name="FormalAlgorithm"):
    """生成索引内容"""
    lines = [
        f"# {project_name} 文档索引",
        "",
        f"> 自动生成于: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "> 使用 `scripts/generate_index.py` 重新生成",
        "",
        "## 目录",
        "",
    ]
    
    # 按类别分组
    categories = defaultdict(list)
    for file in files:
        categories[file['category']].append(file)
    
    # 生成目录
    for category in sorted(categories.keys()):
        lines.append(f"- [{category}](#{category.replace(' ', '-').lower()})")
    lines.append("")
    
    # 生成内容
    for category in sorted(categories.keys()):
        lines.append(f"## {category}")
        lines.append("")
        
        for file in categories[category]:
            path_str = str(file['path']).replace('\\', '/')
            lines.append(f"- [{file['title']}]({path_str})")
            if file['description']:
                lines.append(f"  - {file['description']}")
        
        lines.append("")
    
    # 添加统计信息
    lines.append("---")
    lines.append("")
    lines.append("## 统计信息")
    lines.append("")
    lines.append(f"- 总文档数: {len(files)}")
    lines.append(f"- 类别数: {len(categories)}")
    lines.append("")
    
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='自动生成文档索引',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python generate_index.py
  python generate_index.py -o docs/索引.md
  python generate_index.py -v
        """
    )
    parser.add_argument(
        '--output', '-o',
        default='docs/README.md',
        help='输出文件路径 (默认: docs/README.md)'
    )
    parser.add_argument(
        '--docs-dir', '-d',
        default='docs',
        help='文档目录路径 (默认: docs)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='显示详细信息'
    )
    
    args = parser.parse_args()
    
    # 确定项目根目录
    script_dir = Path(__file__).parent.resolve()
    project_root = script_dir.parent
    docs_dir = project_root / args.docs_dir
    output_file = project_root / args.output
    
    if args.verbose:
        print(f"文档目录: {docs_dir}")
        print(f"输出文件: {output_file}")
    
    # 扫描文档
    print("正在扫描文档...")
    files = scan_docs(docs_dir)
    print(f"找到 {len(files)} 个文档")
    
    if args.verbose:
        for f in files:
            print(f"  - {f['path']}: {f['title']}")
    
    # 生成索引
    print("正在生成索引...")
    index_content = generate_index(files)
    
    # 写入文件
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(index_content)
    
    print(f"索引已生成: {output_file}")


if __name__ == '__main__':
    main()
