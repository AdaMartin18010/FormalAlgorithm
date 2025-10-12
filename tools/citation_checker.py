#!/usr/bin/env python3
"""
引用检查工具 / Citation Checker Tool
用于扫描Markdown文档,检查引用规范性和覆盖率

Usage:
    python tools/citation_checker.py [--path docs/] [--report]
"""

import os
import re
import sys
import yaml
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict

class CitationChecker:
    """引用检查器"""
    
    def __init__(self, references_db_path: str = "docs/references_database.yaml"):
        """初始化引用检查器"""
        self.references_db_path = references_db_path
        self.references = {}
        self.load_references()
        
        # 引用格式正则表达式
        # 匹配 [Author2023] 或 [Author et al. 2023] 格式
        self.citation_pattern = re.compile(r'\[([A-Z][A-Za-z0-9]+(?:\s+et\s+al\.)?\s*\d{4}[a-z]?)\]')
        
    def load_references(self):
        """加载引用数据库"""
        try:
            with open(self.references_db_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
                
            # 展平所有分类的引用
            for category, refs in data.items():
                if isinstance(refs, list):
                    for ref in refs:
                        if 'reference_id' in ref:
                            self.references[ref['reference_id']] = ref
                            
            print(f"✓ 加载了 {len(self.references)} 个引用")
        except Exception as e:
            print(f"✗ 加载引用数据库失败: {e}")
            sys.exit(1)
    
    def extract_citations(self, content: str) -> Set[str]:
        """从文档内容中提取所有引用ID"""
        citations = set()
        matches = self.citation_pattern.findall(content)
        for match in matches:
            # 清理空格
            citation_id = match.replace(' ', '')
            citations.add(citation_id)
        return citations
    
    def check_file(self, filepath: str) -> Dict:
        """检查单个Markdown文件"""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {
                'error': str(e),
                'citations': set(),
                'missing': set(),
                'found': set()
            }
        
        # 提取引用
        citations = self.extract_citations(content)
        
        # 检查引用是否在数据库中
        found = set()
        missing = set()
        for citation in citations:
            if citation in self.references:
                found.add(citation)
            else:
                missing.add(citation)
        
        # 检查是否有参考文献章节
        has_reference_section = bool(re.search(
            r'##\s*参考文献|##\s*References',
            content,
            re.IGNORECASE
        ))
        
        return {
            'citations': citations,
            'found': found,
            'missing': missing,
            'has_reference_section': has_reference_section,
            'citation_count': len(citations)
        }
    
    def scan_directory(self, directory: str = "docs/") -> Dict:
        """扫描目录中的所有Markdown文件"""
        results = {}
        md_files = list(Path(directory).rglob("*.md"))
        
        print(f"\n开始扫描 {len(md_files)} 个Markdown文件...\n")
        
        for filepath in md_files:
            rel_path = str(filepath.relative_to(directory))
            results[rel_path] = self.check_file(str(filepath))
        
        return results
    
    def generate_report(self, results: Dict) -> str:
        """生成检查报告"""
        report = []
        report.append("=" * 80)
        report.append("引用检查报告 / Citation Check Report")
        report.append("=" * 80)
        report.append("")
        
        # 统计数据
        total_files = len(results)
        files_with_citations = sum(1 for r in results.values() if r.get('citation_count', 0) > 0)
        files_with_ref_section = sum(1 for r in results.values() if r.get('has_reference_section', False))
        total_citations = sum(r.get('citation_count', 0) for r in results.values())
        total_missing = sum(len(r.get('missing', set())) for r in results.values())
        
        # 收集所有缺失的引用
        all_missing = set()
        for r in results.values():
            all_missing.update(r.get('missing', set()))
        
        report.append("## 总体统计 / Overall Statistics")
        report.append("")
        report.append(f"- 总文档数: {total_files}")
        report.append(f"- 包含引用的文档: {files_with_citations} ({files_with_citations/total_files*100:.1f}%)")
        report.append(f"- 包含参考文献章节的文档: {files_with_ref_section} ({files_with_ref_section/total_files*100:.1f}%)")
        report.append(f"- 总引用次数: {total_citations}")
        report.append(f"- 缺失引用: {total_missing}")
        report.append(f"- 唯一缺失引用ID: {len(all_missing)}")
        report.append("")
        
        # 引用覆盖率
        if total_files > 0:
            coverage = files_with_ref_section / total_files * 100
            report.append(f"**引用覆盖率**: {coverage:.1f}%")
            report.append("")
        
        # 缺失引用列表
        if all_missing:
            report.append("## 缺失的引用 / Missing Citations")
            report.append("")
            report.append("以下引用在文档中使用但未在引用数据库中找到：")
            report.append("")
            for citation in sorted(all_missing):
                # 找到使用此引用的文件
                files_using = [f for f, r in results.items() if citation in r.get('citations', set())]
                report.append(f"- `{citation}` (使用于 {len(files_using)} 个文件)")
                for f in files_using[:3]:  # 只显示前3个
                    report.append(f"  - {f}")
                if len(files_using) > 3:
                    report.append(f"  - ... 还有 {len(files_using) - 3} 个文件")
            report.append("")
        
        # 需要添加参考文献章节的文档
        files_need_ref_section = [
            f for f, r in results.items()
            if r.get('citation_count', 0) > 0 and not r.get('has_reference_section', False)
        ]
        
        if files_need_ref_section:
            report.append("## 需要添加参考文献章节的文档 / Files Need Reference Section")
            report.append("")
            report.append(f"以下 {len(files_need_ref_section)} 个文档包含引用但缺少参考文献章节：")
            report.append("")
            for f in sorted(files_need_ref_section)[:20]:  # 只显示前20个
                citations = results[f].get('citation_count', 0)
                report.append(f"- {f} ({citations} 个引用)")
            if len(files_need_ref_section) > 20:
                report.append(f"- ... 还有 {len(files_need_ref_section) - 20} 个文件")
            report.append("")
        
        # 引用使用频率统计
        citation_usage = defaultdict(int)
        for r in results.values():
            for citation in r.get('found', set()):
                citation_usage[citation] += 1
        
        if citation_usage:
            report.append("## 引用使用频率 Top 10 / Top 10 Most Used Citations")
            report.append("")
            top_citations = sorted(citation_usage.items(), key=lambda x: x[1], reverse=True)[:10]
            for citation, count in top_citations:
                ref = self.references.get(citation, {})
                title = ref.get('title', {})
                if isinstance(title, dict):
                    title = title.get('en', 'Unknown')
                report.append(f"- `{citation}`: {count} 次")
                report.append(f"  {title[:80]}...")
            report.append("")
        
        # 数据库中未使用的引用
        used_citations = set()
        for r in results.values():
            used_citations.update(r.get('found', set()))
        
        unused_citations = set(self.references.keys()) - used_citations
        if unused_citations:
            report.append(f"## 数据库中未使用的引用 / Unused Citations in Database ({len(unused_citations)})")
            report.append("")
            report.append("以下引用在数据库中但未被任何文档使用：")
            report.append("")
            for citation in sorted(unused_citations)[:20]:  # 只显示前20个
                ref = self.references[citation]
                title = ref.get('title', {})
                if isinstance(title, dict):
                    title = title.get('en', 'Unknown')
                report.append(f"- `{citation}`: {title[:60]}...")
            if len(unused_citations) > 20:
                report.append(f"- ... 还有 {len(unused_citations) - 20} 个引用")
            report.append("")
        
        report.append("=" * 80)
        report.append("报告完成 / Report Complete")
        report.append("=" * 80)
        
        return "\n".join(report)
    
    def generate_detailed_report(self, results: Dict, output_file: str = "citation_report.md"):
        """生成详细报告并保存到文件"""
        report = self.generate_report(results)
        
        # 添加详细的文件列表
        detailed = [report, "", "## 详细文件列表 / Detailed File List", ""]
        
        # 按模块分组
        by_module = defaultdict(list)
        for filepath, result in results.items():
            module = filepath.split('/')[0] if '/' in filepath else 'root'
            by_module[module].append((filepath, result))
        
        for module in sorted(by_module.keys()):
            detailed.append(f"### {module}")
            detailed.append("")
            
            for filepath, result in sorted(by_module[module]):
                citations = result.get('citation_count', 0)
                has_ref = "✓" if result.get('has_reference_section', False) else "✗"
                missing = len(result.get('missing', set()))
                
                status = "✓" if citations > 0 and missing == 0 and result.get('has_reference_section', False) else "⚠"
                
                detailed.append(f"- {status} `{filepath}`")
                detailed.append(f"  - 引用数: {citations}, 参考文献章节: {has_ref}, 缺失: {missing}")
                
                if result.get('missing'):
                    detailed.append(f"  - 缺失引用: {', '.join(sorted(result['missing']))}")
            detailed.append("")
        
        # 保存到文件
        output_path = Path(output_file)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(detailed))
        
        print(f"\n✓ 详细报告已保存到: {output_file}")
        
        return '\n'.join(detailed)


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='检查Markdown文档中的引用')
    parser.add_argument('--path', default='docs/', help='要扫描的目录路径')
    parser.add_argument('--db', default='docs/references_database.yaml', help='引用数据库路径')
    parser.add_argument('--report', action='store_true', help='生成详细报告文件')
    parser.add_argument('--output', default='citation_report.md', help='报告输出文件名')
    
    args = parser.parse_args()
    
    # 创建检查器
    checker = CitationChecker(args.db)
    
    # 扫描目录
    results = checker.scan_directory(args.path)
    
    # 生成并显示报告
    if args.report:
        report = checker.generate_detailed_report(results, args.output)
    else:
        report = checker.generate_report(results)
    
    print(report)


if __name__ == "__main__":
    main()

