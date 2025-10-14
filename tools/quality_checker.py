#!/usr/bin/env python3
"""
文档质量检查脚本
检查文档的理论深度、内容准确性和工程化程度
"""

import os
import re
import yaml
from pathlib import Path
from datetime import datetime

class DocumentQualityChecker:
    def __init__(self, docs_path="docs"):
        self.docs_path = Path(docs_path)
        self.issues = []
        
    def check_document(self, doc_path):
        """检查单个文档的质量"""
        with open(doc_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
        issues = []
        
        # 检查理论深度
        issues.extend(self.check_theoretical_depth(content))
        
        # 检查内容准确性
        issues.extend(self.check_content_accuracy(content))
        
        # 检查工程化程度
        issues.extend(self.check_engineering_quality(content))
        
        return issues
    
    def check_theoretical_depth(self, content):
        """检查理论深度"""
        issues = []
        
        # 检查是否有严格定义
        if not re.search(r'\*\*定义\s+\d+\.\d+\*\*', content):
            issues.append("缺少严格的形式化定义")
            
        # 检查是否有定理证明
        if not re.search(r'\*\*定理\s+\d+\.\d+\*\*', content):
            issues.append("缺少定理和证明")
            
        # 检查数学符号使用
        if not re.search(r'\$\$.*\$\$', content):
            issues.append("缺少数学公式")
            
        # 检查公理定义
        if not re.search(r'\*\*公理\s+\d+\.\d+\*\*', content):
            issues.append("缺少公理定义")
            
        return issues
    
    def check_content_accuracy(self, content):
        """检查内容准确性"""
        issues = []
        
        # 检查引用格式
        if not re.search(r'\[.*\d{4}\]', content):
            issues.append("缺少规范引用")
            
        # 检查概念定义
        if not re.search(r'\*\*定义\s+\d+\.\d+\*\*', content):
            issues.append("缺少概念定义")
            
        # 检查参考文献章节
        if not re.search(r'## 参考文献', content):
            issues.append("缺少参考文献章节")
            
        return issues
    
    def check_engineering_quality(self, content):
        """检查工程化程度"""
        issues = []
        
        # 检查代码示例
        if not re.search(r'```rust', content):
            issues.append("缺少Rust代码示例")
            
        # 检查测试用例
        if not re.search(r'#\[test\]', content):
            issues.append("缺少测试用例")
            
        # 检查性能分析
        if not re.search(r'性能|performance|复杂度|complexity', content, re.IGNORECASE):
            issues.append("缺少性能分析")
            
        return issues
    
    def generate_report(self):
        """生成质量检查报告"""
        report = []
        
        for doc_path in self.docs_path.rglob("*.md"):
            if doc_path.name.startswith("_"):
                continue
                
            issues = self.check_document(doc_path)
            if issues:
                report.append({
                    'document': str(doc_path),
                    'issues': issues
                })
        
        return report

if __name__ == "__main__":
    checker = DocumentQualityChecker()
    report = checker.generate_report()
    
    print("# 文档质量检查报告")
    print(f"检查时间: {datetime.now()}")
    print(f"检查文档数: {len(report)}")
    print()
    
    for item in report:
        print(f"## {item['document']}")
        for issue in item['issues']:
            print(f"- ❌ {issue}")
        print()
    
    # 保存报告
    with open('quality_check_report.yaml', 'w', encoding='utf-8') as f:
        yaml.dump(report, f, default_flow_style=False, allow_unicode=True)
