#!/usr/bin/env python3
"""
引用检查工具
检查文档中的学术引用规范性

功能：
- 扫描文档中的定义、定理、算法
- 检查是否有对应的引用
- 验证引用格式是否符合ACM标准
- 检查引用ID是否存在于数据库
"""

import re
import yaml
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional
from collections import defaultdict
import sys


@dataclass
class CitationIssue:
    """引用问题记录"""
    file: str
    line: int
    type: str  # 'missing', 'format', 'invalid_id', 'structure'
    severity: str  # 'error', 'warning', 'info'
    message: str
    context: str = ""


class ReferenceDatabase:
    """引用数据库管理器"""
    
    def __init__(self):
        self.references: Dict[str, dict] = {}
        self.authors: Dict[str, str] = {}  # author -> reference_id
        
    def load_from_yaml_blocks(self, content: str) -> None:
        """从Markdown中的YAML代码块加载引用"""
        # 提取YAML代码块
        yaml_pattern = r'```yaml\n(.*?)```'
        yaml_blocks = re.findall(yaml_pattern, content, re.DOTALL)
        
        for block in yaml_blocks:
            try:
                refs = yaml.safe_load(block)
                if isinstance(refs, list):
                    for ref in refs:
                        if isinstance(ref, dict) and 'reference_id' in ref:
                            ref_id = ref['reference_id']
                            self.references[ref_id] = ref
                            # 索引作者
                            if 'authors' in ref:
                                for author in ref['authors']:
                                    last_name = author.split()[-1] if author else ""
                                    if last_name:
                                        self.authors[last_name] = ref_id
            except yaml.YAMLError as e:
                print(f"Warning: Failed to parse YAML block: {e}")
    
    def load_from_file(self, db_path: Path) -> None:
        """从文件加载引用数据库"""
        if not db_path.exists():
            raise FileNotFoundError(f"引用数据库未找到: {db_path}")
        
        content = db_path.read_text(encoding='utf-8')
        self.load_from_yaml_blocks(content)
        
    def is_valid_id(self, ref_id: str) -> bool:
        """检查引用ID是否有效"""
        return ref_id in self.references
    
    def get_reference(self, ref_id: str) -> Optional[dict]:
        """获取引用信息"""
        return self.references.get(ref_id)
    
    def get_stats(self) -> dict:
        """获取数据库统计信息"""
        return {
            'total': len(self.references),
            'classic': sum(1 for r in self.references.values() if r.get('quality') == 'classic'),
            'standard': sum(1 for r in self.references.values() if r.get('quality') == 'standard'),
            'recent': sum(1 for r in self.references.values() if r.get('quality') == 'recent'),
        }


class CitationChecker:
    """引用检查器"""
    
    # ACM标准引用格式模式
    ACM_CITATION_PATTERN = re.compile(
        r'\[([A-Z][a-zA-Z]+(?:\s+et\s+al\.)?\s+\d{4}[a-z]?)\]'
    )
    
    # 定义/定理/算法模式
    DEFINITION_PATTERN = re.compile(
        r'^\s*\*\*定义\s*[\d.]*\*\*\s*\(([^)]+)\)',
        re.MULTILINE
    )
    THEOREM_PATTERN = re.compile(
        r'^\s*\*\*定理\s*[\d.]*\*\*\s*\(([^)]+)\)',
        re.MULTILINE
    )
    ALGORITHM_PATTERN = re.compile(
        r'^\s*\*\*算法\s*[\d.]*\*\*\s*\(([^)]+)\)',
        re.MULTILINE
    )
    PROPERTY_PATTERN = re.compile(
        r'^\s*\*\*性质\s*[\d.]*\*\*\s*\(([^)]+)\)',
        re.MULTILINE
    )
    
    # 引用后缺失检查 - 定义/定理/算法行后应该跟引用
    DEF_WITH_CITATION = re.compile(
        r'\*\*定义\s*[\d.]*\*\*\s*\([^)]+\)\s*\[([^\]]+)\]'
    )
    THEOREM_WITH_CITATION = re.compile(
        r'\*\*定理\s*[\d.]*\*\*\s*\([^)]+\)\s*\[([^\]]+)\]'
    )
    ALGORITHM_WITH_CITATION = re.compile(
        r'\*\*算法\s*[\d.]*\*\*\s*\([^)]+\)\s*\[([^\]]+)\]'
    )
    
    def __init__(self, ref_db: ReferenceDatabase):
        self.ref_db = ref_db
        self.issues: List[CitationIssue] = []
        
    def check_file(self, file_path: Path) -> List[CitationIssue]:
        """检查单个文件的引用问题"""
        issues = []
        content = file_path.read_text(encoding='utf-8')
        lines = content.split('\n')
        
        # 1. 检查定义后是否有引用
        issues.extend(self._check_definitions_have_citations(file_path, lines))
        
        # 2. 检查定理后是否有引用
        issues.extend(self._check_theorems_have_citations(file_path, lines))
        
        # 3. 检查算法后是否有引用
        issues.extend(self._check_algorithms_have_citations(file_path, lines))
        
        # 4. 检查引用ID有效性
        issues.extend(self._check_citation_ids(file_path, lines))
        
        # 5. 检查ACM格式
        issues.extend(self._check_acm_format(file_path, lines))
        
        # 6. 检查参考文献章节
        issues.extend(self._check_references_section(file_path, content))
        
        return issues
    
    def _check_definitions_have_citations(
        self, file_path: Path, lines: List[str]
    ) -> List[CitationIssue]:
        """检查定义后是否有引用"""
        issues = []
        
        for i, line in enumerate(lines, 1):
            # 匹配定义行
            if re.search(r'\*\*定义\s*[\d.]*\*\*\s*\([^)]+\)', line):
                # 检查同一行或接下来2行内是否有引用
                context_lines = lines[i-1:min(i+2, len(lines))]
                context = '\n'.join(context_lines)
                
                if not re.search(r'\[[A-Z][a-zA-Z]+\s+\d{4}', context):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='missing',
                        severity='warning',
                        message=f'定义后可能缺少引用',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_theorems_have_citations(
        self, file_path: Path, lines: List[str]
    ) -> List[CitationIssue]:
        """检查定理后是否有引用"""
        issues = []
        
        for i, line in enumerate(lines, 1):
            if re.search(r'\*\*定理\s*[\d.]*\*\*\s*\([^)]+\)', line):
                context_lines = lines[i-1:min(i+2, len(lines))]
                context = '\n'.join(context_lines)
                
                if not re.search(r'\[[A-Z][a-zA-Z]+\s+\d{4}', context):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='missing',
                        severity='warning',
                        message=f'定理后可能缺少引用',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_algorithms_have_citations(
        self, file_path: Path, lines: List[str]
    ) -> List[CitationIssue]:
        """检查算法后是否有引用"""
        issues = []
        
        for i, line in enumerate(lines, 1):
            if re.search(r'\*\*算法\s*[\d.]*\*\*\s*\([^)]+\)', line):
                context_lines = lines[i-1:min(i+2, len(lines))]
                context = '\n'.join(context_lines)
                
                if not re.search(r'\[[A-Z][a-zA-Z]+\s+\d{4}', context):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='missing',
                        severity='info',
                        message=f'算法后可能缺少引用',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_citation_ids(
        self, file_path: Path, lines: List[str]
    ) -> List[CitationIssue]:
        """检查引用ID是否存在于数据库"""
        issues = []
        
        for i, line in enumerate(lines, 1):
            # 匹配作者年份格式引用
            for match in self.ACM_CITATION_PATTERN.finditer(line):
                citation = match.group(1)
                # 规范化引用ID
                ref_id = citation.replace(' ', '').replace('et al.', '')
                
                if not self.ref_db.is_valid_id(ref_id):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='invalid_id',
                        severity='warning',
                        message=f'引用ID可能不在数据库中: {citation}',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_acm_format(
        self, file_path: Path, lines: List[str]
    ) -> List[CitationIssue]:
        """检查ACM引用格式"""
        issues = []
        
        for i, line in enumerate(lines, 1):
            # 检查常见格式错误
            # 1. 检查是否使用数字引用 [1], [2] 等（应使用作者-年份格式）
            if re.search(r'\[\d+\](?!\()', line):
                # 排除Markdown链接 [text](url) 的情况
                if not re.search(r'\[\d+\]\([^)]+\)', line):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='format',
                        severity='info',
                        message='使用数字引用格式，推荐ACM作者-年份格式 [Author Year]',
                        context=line[:80]
                    ))
            
            # 2. 检查页码范围是否使用en-dash
            if 'pp. ' in line or 'pages ' in line:
                if re.search(r'\d+\s*-\s*\d+', line) and not re.search(r'\d+\s*–\s*\d+', line):
                    issues.append(CitationIssue(
                        file=str(file_path),
                        line=i,
                        type='format',
                        severity='info',
                        message='页码范围应使用en-dash (–) 而非连字符 (-)',
                        context=line[:80]
                    ))
        
        return issues
    
    def _check_references_section(
        self, file_path: Path, content: str
    ) -> List[CitationIssue]:
        """检查参考文献章节"""
        issues = []
        
        # 检查是否有参考文献章节
        if '## 参考文献' not in content and '## References' not in content:
            issues.append(CitationIssue(
                file=str(file_path),
                line=0,
                type='structure',
                severity='warning',
                message='文档缺少参考文献章节',
                context=""
            ))
        
        return issues


def load_reference_database(db_path: Path) -> ReferenceDatabase:
    """加载引用数据库"""
    db = ReferenceDatabase()
    db.load_from_file(db_path)
    return db


def main():
    """主函数"""
    # 默认数据库路径
    db_path = Path('docs/引用数据库-扩展版-2025.md')
    
    # 允许通过参数指定数据库
    if len(sys.argv) > 1:
        db_path = Path(sys.argv[1])
    
    # 加载引用数据库
    try:
        ref_db = load_reference_database(db_path)
        stats = ref_db.get_stats()
        print(f"📚 引用数据库加载成功: {stats['total']} 条引用")
        print(f"   - Classic: {stats['classic']}, Standard: {stats['standard']}, Recent: {stats['recent']}")
        print()
    except FileNotFoundError as e:
        print(f"❌ 错误: {e}")
        sys.exit(1)
    
    # 创建检查器
    checker = CitationChecker(ref_db)
    
    # 扫描文档
    doc_path = Path('docs')
    all_issues = []
    checked_files = 0
    
    for md_file in doc_path.rglob('*.md'):
        # 跳过特定文件
        if any(skip in str(md_file) for skip in ['README', '任务完成报告', '质量报告']):
            continue
        
        issues = checker.check_file(md_file)
        all_issues.extend(issues)
        checked_files += 1
    
    # 输出报告
    print("=" * 60)
    print("📋 引用检查报告")
    print("=" * 60)
    print(f"检查文档数: {checked_files}")
    print(f"发现问题数: {len(all_issues)}")
    print()
    
    # 按严重程度统计
    severity_count = defaultdict(int)
    type_count = defaultdict(int)
    
    for issue in all_issues:
        severity_count[issue.severity] += 1
        type_count[issue.type] += 1
    
    print("按严重程度:")
    for sev, count in sorted(severity_count.items(), 
                              key=lambda x: {'error': 0, 'warning': 1, 'info': 2}[x[0]]):
        icon = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}[sev]
        print(f"  {icon} {sev}: {count}")
    
    print("\n按问题类型:")
    for typ, count in type_count.items():
        print(f"  - {typ}: {count}")
    
    print("\n" + "=" * 60)
    print("详细问题列表 (前20个):")
    print("=" * 60)
    
    for i, issue in enumerate(all_issues[:20], 1):
        icon = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}[issue.severity]
        print(f"\n{i}. {icon} [{issue.type}] {issue.file}:{issue.line}")
        print(f"   消息: {issue.message}")
        if issue.context:
            print(f"   上下文: {issue.context[:60]}...")
    
    if len(all_issues) > 20:
        print(f"\n... 还有 {len(all_issues) - 20} 个问题未显示")
    
    # 返回退出码
    error_count = severity_count.get('error', 0)
    warning_count = severity_count.get('warning', 0)
    
    print("\n" + "=" * 60)
    if error_count > 0:
        print(f"❌ 检查完成，发现 {error_count} 个错误")
        sys.exit(1)
    elif warning_count > 0:
        print(f"⚠️  检查完成，发现 {warning_count} 个警告")
        sys.exit(0)
    else:
        print("✅ 检查完成，未发现引用问题")
        sys.exit(0)


if __name__ == '__main__':
    main()
