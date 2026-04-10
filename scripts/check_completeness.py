#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
检查项目完整性脚本

功能：
- 检查项目必要的文件和目录是否存在
- 验证文档的完整性和一致性
- 检查链接的有效性
- 生成完整性报告

使用方法：
    python check_completeness.py [options]

选项：
    --fix, -f       尝试自动修复发现的问题
    --output, -o    输出报告文件路径
    --verbose, -v   显示详细信息
    --help, -h      显示帮助信息
"""

import os
import re
import argparse
from pathlib import Path
from collections import defaultdict
from datetime import datetime
from urllib.parse import urlparse


# 项目必要的文件和目录
REQUIRED_FILES = [
    'README.md',
    'LICENSE',
    'CODE_OF_CONDUCT.md',
]

REQUIRED_DIRS = [
    'docs',
    'scripts',
]

# 推荐的文件和目录
RECOMMENDED_FILES = [
    '.gitignore',
    'CONTRIBUTING.md',
    'CHANGELOG.md',
    'docs/README.md',
    'docs/FAQ.md',
]

RECOMMENDED_DIRS = [
    '.github',
    'examples',
    'tools',
]

# 文档完整性检查项
DOC_CHECKS = {
    'has_title': '是否有标题',
    'has_description': '是否有描述',
    'has_toc': '是否有目录',
    'proper_headers': '标题层级是否正确',
    'no_broken_links': '链接是否有效',
}


class CompletenessChecker:
    def __init__(self, project_root):
        self.project_root = Path(project_root)
        self.issues = []
        self.warnings = []
        self.info = []
        self.fixed = []
    
    def check_required_files(self):
        """检查必要的文件"""
        for file in REQUIRED_FILES:
            file_path = self.project_root / file
            if file_path.exists():
                self.info.append(f"✓ 必要文件存在: {file}")
            else:
                self.issues.append(f"✗ 缺少必要文件: {file}")
    
    def check_required_dirs(self):
        """检查必要的目录"""
        for dir in REQUIRED_DIRS:
            dir_path = self.project_root / dir
            if dir_path.exists() and dir_path.is_dir():
                self.info.append(f"✓ 必要目录存在: {dir}")
            else:
                self.issues.append(f"✗ 缺少必要目录: {dir}")
    
    def check_recommended_files(self):
        """检查推荐的文件"""
        for file in RECOMMENDED_FILES:
            file_path = self.project_root / file
            if file_path.exists():
                self.info.append(f"✓ 推荐文件存在: {file}")
            else:
                self.warnings.append(f"⚠ 缺少推荐文件: {file}")
    
    def check_recommended_dirs(self):
        """检查推荐的目录"""
        for dir in RECOMMENDED_DIRS:
            dir_path = self.project_root / dir
            if dir_path.exists() and dir_path.is_dir():
                self.info.append(f"✓ 推荐目录存在: {dir}")
            else:
                self.warnings.append(f"⚠ 缺少推荐目录: {dir}")
    
    def check_readme(self):
        """检查 README.md 的完整性"""
        readme_path = self.project_root / 'README.md'
        if not readme_path.exists():
            return
        
        try:
            content = readme_path.read_text(encoding='utf-8')
            
            # 检查是否有项目标题
            if not re.search(r'^#\s+\S+', content, re.MULTILINE):
                self.warnings.append("⚠ README.md 缺少项目标题")
            
            # 检查是否有描述
            lines = content.split('\n')
            has_desc = False
            for i, line in enumerate(lines):
                if line.startswith('# ') and i + 1 < len(lines):
                    next_lines = '\n'.join(lines[i+1:i+4])
                    if next_lines.strip() and not next_lines.startswith('#'):
                        has_desc = True
                        break
            
            if not has_desc:
                self.warnings.append("⚠ README.md 缺少项目描述")
            
            # 检查是否有安装说明
            if not re.search(r'##?\s*(安装|Install)', content, re.IGNORECASE):
                self.warnings.append("⚠ README.md 缺少安装说明")
            
            # 检查是否有使用说明
            if not re.search(r'##?\s*(使用|Usage|用法)', content, re.IGNORECASE):
                self.warnings.append("⚠ README.md 缺少使用说明")
            
            # 检查是否有许可证信息
            if 'LICENSE' not in content and '许可' not in content:
                self.warnings.append("⚠ README.md 缺少许可证信息")
            
        except Exception as e:
            self.issues.append(f"✗ 无法读取 README.md: {e}")
    
    def check_docs(self):
        """检查文档的完整性"""
        docs_dir = self.project_root / 'docs'
        if not docs_dir.exists():
            return
        
        md_files = list(docs_dir.rglob('*.md'))
        
        if len(md_files) == 0:
            self.warnings.append("⚠ docs/ 目录下没有 Markdown 文件")
            return
        
        self.info.append(f"✓ 找到 {len(md_files)} 个文档文件")
        
        # 检查每个文档
        broken_links = []
        for md_file in md_files:
            try:
                content = md_file.read_text(encoding='utf-8')
                rel_path = md_file.relative_to(self.project_root)
                
                # 检查是否有标题
                if not re.search(r'^#\s+\S+', content, re.MULTILINE):
                    self.warnings.append(f"⚠ {rel_path} 缺少标题")
                
                # 检查内部链接
                links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
                for text, link in links:
                    if link.startswith('#') or link.startswith('http'):
                        continue
                    
                    # 解析相对链接
                    if link.startswith('/'):
                        target = self.project_root / link[1:]
                    else:
                        target = md_file.parent / link
                    
                    target = target.resolve()
                    
                    if not target.exists():
                        broken_links.append(f"{rel_path} -> {link}")
                
            except Exception as e:
                self.warnings.append(f"⚠ 无法读取 {rel_path}: {e}")
        
        if broken_links:
            self.warnings.append(f"⚠ 发现 {len(broken_links)} 个无效链接:")
            for link in broken_links[:10]:  # 最多显示10个
                self.warnings.append(f"    {link}")
            if len(broken_links) > 10:
                self.warnings.append(f"    ... 还有 {len(broken_links) - 10} 个")
    
    def check_gitignore(self):
        """检查 .gitignore 的完整性"""
        gitignore_path = self.project_root / '.gitignore'
        
        recommended_patterns = [
            '*.log',
            '.env',
            '__pycache__/',
            'node_modules/',
            '.DS_Store',
            'Thumbs.db',
        ]
        
        if gitignore_path.exists():
            try:
                content = gitignore_path.read_text(encoding='utf-8')
                missing = []
                for pattern in recommended_patterns:
                    if pattern not in content:
                        missing.append(pattern)
                
                if missing:
                    self.warnings.append(f"⚠ .gitignore 可能缺少以下模式: {', '.join(missing)}")
                else:
                    self.info.append("✓ .gitignore 看起来完整")
                    
            except Exception as e:
                self.warnings.append(f"⚠ 无法读取 .gitignore: {e}")
        else:
            self.warnings.append("⚠ 缺少 .gitignore 文件")
    
    def check_license(self):
        """检查许可证文件"""
        license_files = ['LICENSE', 'LICENSE.md', 'LICENSE.txt', 'COPYING']
        found = False
        
        for fname in license_files:
            if (self.project_root / fname).exists():
                found = True
                self.info.append(f"✓ 找到许可证文件: {fname}")
                break
        
        if not found:
            self.warnings.append("⚠ 未找到许可证文件")
    
    def run_all_checks(self):
        """运行所有检查"""
        print("正在检查项目完整性...")
        
        print("  检查必要文件...")
        self.check_required_files()
        
        print("  检查必要目录...")
        self.check_required_dirs()
        
        print("  检查推荐文件...")
        self.check_recommended_files()
        
        print("  检查推荐目录...")
        self.check_recommended_dirs()
        
        print("  检查 README.md...")
        self.check_readme()
        
        print("  检查文档...")
        self.check_docs()
        
        print("  检查 .gitignore...")
        self.check_gitignore()
        
        print("  检查许可证...")
        self.check_license()
        
        print("检查完成！")
    
    def generate_report(self):
        """生成检查报告"""
        lines = [
            "# 项目完整性检查报告",
            "",
            f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"项目路径: {self.project_root}",
            "",
            "## 摘要",
            "",
            f"- 问题: {len(self.issues)}",
            f"- 警告: {len(self.warnings)}",
            f"- 信息: {len(self.info)}",
            "",
        ]
        
        if self.issues:
            lines.extend([
                "## 问题",
                "",
            ])
            for issue in self.issues:
                lines.append(f"- {issue}")
            lines.append("")
        
        if self.warnings:
            lines.extend([
                "## 警告",
                "",
            ])
            for warning in self.warnings:
                lines.append(f"- {warning}")
            lines.append("")
        
        if self.info:
            lines.extend([
                "## 信息",
                "",
            ])
            for info in self.info:
                lines.append(f"- {info}")
            lines.append("")
        
        lines.extend([
            "---",
            "",
            "*由 scripts/check_completeness.py 生成*",
        ])
        
        return '\n'.join(lines)
    
    def print_summary(self):
        """打印摘要"""
        print("\n" + "=" * 50)
        print("检查摘要")
        print("=" * 50)
        print(f"问题: {len(self.issues)}")
        print(f"警告: {len(self.warnings)}")
        print(f"信息: {len(self.info)}")
        
        if self.issues:
            print("\n发现的问题:")
            for issue in self.issues:
                print(f"  {issue}")
        
        if self.warnings:
            print("\n建议关注的警告:")
            for warning in self.warnings[:5]:
                print(f"  {warning}")
            if len(self.warnings) > 5:
                print(f"  ... 还有 {len(self.warnings) - 5} 个警告")


def main():
    parser = argparse.ArgumentParser(
        description='检查项目完整性',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python check_completeness.py
  python check_completeness.py -v
  python check_completeness.py -o report.md
        """
    )
    parser.add_argument(
        '--output', '-o',
        help='输出报告文件路径'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='显示详细信息'
    )
    parser.add_argument(
        '--path', '-p',
        default='.',
        help='项目路径 (默认: 当前目录)'
    )
    
    args = parser.parse_args()
    
    # 确定项目根目录
    if args.path == '.':
        script_dir = Path(__file__).parent.resolve()
        project_root = script_dir.parent
    else:
        project_root = Path(args.path).resolve()
    
    # 运行检查
    checker = CompletenessChecker(project_root)
    checker.run_all_checks()
    
    # 打印摘要
    checker.print_summary()
    
    # 生成并保存报告
    report = checker.generate_report()
    
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"\n报告已保存: {output_path}")
    elif args.verbose:
        print("\n" + report)
    
    # 返回退出码
    return 1 if checker.issues else 0


if __name__ == '__main__':
    exit(main())
