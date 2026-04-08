#!/usr/bin/env python3
"""
文档结构检查工具
检查Markdown文档结构规范性

功能：
- 检查文档是否包含必要章节
- 检查文档头信息
- 检查知识导航链接
- 检查交叉引用
"""

import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional
from collections import defaultdict
import sys


@dataclass
class StructureIssue:
    """文档结构问题记录"""
    file: str
    line: int
    type: str  # 'missing_section', 'header', 'link', 'format'
    severity: str  # 'error', 'warning', 'info'
    message: str
    context: str = ""


# 必需章节（根据文档类型）
REQUIRED_SECTIONS = {
    'standard': [
        '## 摘要',
        '## 学习目标',
        '## 参考文献',
    ],
    'algorithm': [
        '## 摘要',
        '## 形式化定义',
        '## 复杂度分析',
        '## 参考文献',
    ],
    'theory': [
        '## 摘要',
        '## 定理',
        '## 证明',
        '## 参考文献',
    ],
}

# 文档头必需字段
REQUIRED_HEADER_FIELDS = [
    '版本',
    '创建日期',
    '状态',
]


class DocStructureChecker:
    """文档结构检查器"""
    
    def __init__(self, docs_path: Path):
        self.docs_path = docs_path
        self.all_files: Set[Path] = set()
        self._scan_all_files()
        
    def _scan_all_files(self) -> None:
        """扫描所有文档文件"""
        if self.docs_path.exists():
            for md_file in self.docs_path.rglob('*.md'):
                self.all_files.add(md_file.resolve())
    
    def check_file(self, file_path: Path) -> List[StructureIssue]:
        """检查单个文档的结构"""
        issues = []
        
        try:
            content = file_path.read_text(encoding='utf-8')
        except Exception as e:
            return [StructureIssue(
                file=str(file_path),
                line=0,
                type='format',
                severity='error',
                message=f'无法读取文件: {e}'
            )]
        
        lines = content.split('\n')
        
        # 1. 检查文档头
        issues.extend(self._check_header(file_path, content, lines))
        
        # 2. 检查必要章节
        issues.extend(self._check_required_sections(file_path, content))
        
        # 3. 检查链接
        issues.extend(self._check_links(file_path, content, lines))
        
        # 4. 检查标题层级
        issues.extend(self._check_heading_levels(file_path, lines))
        
        # 5. 检查文档完整性
        issues.extend(self._check_document_completeness(file_path, content, lines))
        
        return issues
    
    def _check_header(
        self, file_path: Path, content: str, lines: List[str]
    ) -> List[StructureIssue]:
        """检查文档头信息"""
        issues = []
        
        # 检查是否有文档头（通常以 > 开头的块）
        header_pattern = re.compile(r'^> \*\*([^*]+)\*\*:', re.MULTILINE)
        found_fields = set(header_pattern.findall(content))
        
        # 检查必需字段
        for field in REQUIRED_HEADER_FIELDS:
            if field not in found_fields:
                issues.append(StructureIssue(
                    file=str(file_path),
                    line=1,
                    type='header',
                    severity='warning',
                    message=f'文档头缺少字段: {field}'
                ))
        
        # 检查是否有主标题
        title_pattern = re.compile(r'^# (.+)$', re.MULTILINE)
        if not title_pattern.search(content):
            issues.append(StructureIssue(
                file=str(file_path),
                line=1,
                type='header',
                severity='warning',
                message='文档缺少主标题 (H1)'
            ))
        
        return issues
    
    def _check_required_sections(
        self, file_path: Path, content: str
    ) -> List[StructureIssue]:
        """检查必要章节"""
        issues = []
        
        # 根据内容判断文档类型
        doc_type = self._detect_doc_type(content)
        
        # 获取该类型必需的章节
        required = REQUIRED_SECTIONS.get(doc_type, REQUIRED_SECTIONS['standard'])
        
        # 检查每个必需章节
        for section in required:
            section_name = section.replace('## ', '')
            # 支持中英文
            if section not in content and section_name not in content:
                # 尝试英文版本
                en_section = self._get_english_section(section_name)
                if en_section and en_section not in content:
                    issues.append(StructureIssue(
                        file=str(file_path),
                        line=0,
                        type='missing_section',
                        severity='info',
                        message=f'缺少章节: {section_name}'
                    ))
        
        return issues
    
    def _detect_doc_type(self, content: str) -> str:
        """检测文档类型"""
        if '算法' in content or 'Algorithm' in content:
            if '复杂度' in content or 'Complexity' in content:
                return 'algorithm'
        if '定理' in content or 'Theorem' in content:
            return 'theory'
        return 'standard'
    
    def _get_english_section(self, section_name: str) -> Optional[str]:
        """获取章节的英文版本"""
        translations = {
            '摘要': 'Executive Summary',
            '学习目标': 'Learning Objectives',
            '参考文献': 'References',
            '形式化定义': 'Formal Definition',
            '复杂度分析': 'Complexity Analysis',
            '定理': 'Theorem',
            '证明': 'Proof',
        }
        return translations.get(section_name)
    
    def _check_links(
        self, file_path: Path, content: str, lines: List[str]
    ) -> List[StructureIssue]:
        """检查链接有效性"""
        issues = []
        
        # 匹配Markdown链接 [text](target)
        link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
        
        for i, line in enumerate(lines, 1):
            for match in link_pattern.finditer(line):
                link_text = match.group(1)
                link_target = match.group(2)
                
                # 跳过外部链接和锚点链接
                if link_target.startswith(('http://', 'https://', '#', 'mailto:')):
                    continue
                
                # 跳过图片
                if link_text.startswith('!'):
                    continue
                
                # 解析相对路径
                target_path = self._resolve_link(file_path, link_target)
                
                if target_path and not target_path.exists():
                    issues.append(StructureIssue(
                        file=str(file_path),
                        line=i,
                        type='link',
                        severity='warning',
                        message=f'链接目标不存在: {link_target}',
                        context=line[:80]
                    ))
        
        return issues
    
    def _resolve_link(self, source_file: Path, link_target: str) -> Optional[Path]:
        """解析链接目标路径"""
        # 移除URL参数和锚点
        clean_target = link_target.split('#')[0].split('?')[0]
        
        if not clean_target:
            return None
        
        # 相对路径
        if clean_target.startswith('./'):
            target = source_file.parent / clean_target[2:]
        elif clean_target.startswith('../'):
            target = source_file.parent / clean_target
        else:
            target = source_file.parent / clean_target
        
        # 尝试添加.md扩展名
        if not target.suffix:
            target = target.with_suffix('.md')
        
        return target.resolve() if target.exists() else target
    
    def _check_heading_levels(
        self, file_path: Path, lines: List[str]
    ) -> List[StructureIssue]:
        """检查标题层级"""
        issues = []
        
        prev_level = 0
        for i, line in enumerate(lines, 1):
            heading_match = re.match(r'^(#{1,6})\s+(.+)$', line)
            if heading_match:
                level = len(heading_match.group(1))
                
                # 检查标题层级跳跃
                if prev_level > 0 and level > prev_level + 1:
                    issues.append(StructureIssue(
                        file=str(file_path),
                        line=i,
                        type='format',
                        severity='info',
                        message=f'标题层级跳跃: H{prev_level} -> H{level}',
                        context=line[:80]
                    ))
                
                # 检查标题内容
                title = heading_match.group(2).strip()
                if not title:
                    issues.append(StructureIssue(
                        file=str(file_path),
                        line=i,
                        type='format',
                        severity='warning',
                        message='空标题',
                        context=line[:80]
                    ))
                
                prev_level = level
        
        return issues
    
    def _check_document_completeness(
        self, file_path: Path, content: str, lines: List[str]
    ) -> List[StructureIssue]:
        """检查文档完整性"""
        issues = []
        
        # 检查是否有TODO标记
        todo_pattern = re.compile(r'TODO|FIXME|XXX', re.IGNORECASE)
        for i, line in enumerate(lines, 1):
            if todo_pattern.search(line):
                issues.append(StructureIssue(
                    file=str(file_path),
                    line=i,
                    type='format',
                    severity='info',
                    message='文档包含TODO/FIXME标记',
                    context=line[:80]
                ))
        
        # 检查代码块是否闭合
        code_block_count = content.count('```')
        if code_block_count % 2 != 0:
            issues.append(StructureIssue(
                file=str(file_path),
                line=0,
                type='format',
                severity='error',
                message='代码块未正确闭合（奇数个 ```）'
            ))
        
        # 检查是否有表格格式错误
        for i, line in enumerate(lines, 1):
            if '|' in line:
                # 简单检查表格行
                cells = line.count('|')
                if cells > 1 and not line.strip().startswith('|'):
                    issues.append(StructureIssue(
                        file=str(file_path),
                        line=i,
                        type='format',
                        severity='info',
                        message='表格行可能格式不正确',
                        context=line[:80]
                    ))
        
        return issues


def main():
    """主函数"""
    doc_path = Path('docs')
    
    if not doc_path.exists():
        print(f"❌ 错误: 文档目录不存在: {doc_path}")
        sys.exit(1)
    
    checker = DocStructureChecker(doc_path)
    all_issues = []
    checked_files = 0
    
    # 扫描所有Markdown文件
    for md_file in doc_path.rglob('*.md'):
        # 跳过特定文件
        if any(skip in str(md_file) for skip in ['README', '任务完成报告', '质量报告']):
            continue
        
        issues = checker.check_file(md_file)
        all_issues.extend(issues)
        checked_files += 1
    
    # 输出报告
    print("=" * 60)
    print("📄 文档结构检查报告")
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
    
    # 结构健康度统计
    print("\n" + "=" * 60)
    print("📊 文档结构健康度:")
    print("=" * 60)
    
    header_count = sum(1 for i in all_issues if i.type == 'header')
    link_count = sum(1 for i in all_issues if i.type == 'link')
    section_count = sum(1 for i in all_issues if i.type == 'missing_section')
    
    print(f"  文档头问题: {header_count} 个文档")
    print(f"  链接问题: {link_count} 个")
    print(f"  缺少章节: {section_count} 个")
    
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
        print("✅ 检查完成，文档结构良好")
        sys.exit(0)


if __name__ == '__main__':
    main()
