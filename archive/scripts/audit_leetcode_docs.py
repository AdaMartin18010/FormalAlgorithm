#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LeetCode算法面试专题 - 形式化完整性质量审计脚本
"""

import os
import re
import glob
from collections import defaultdict
from datetime import datetime

BASE_DIR = r"e:\_src\FormalAlgorithm\docs\13-LeetCode算法面试专题"

REQUIRED_FM_KEYS = ["title", "version", "status", "last_updated", "owner", "concepts", "level"]

def get_all_md_files():
    files = []
    for root, _, filenames in os.walk(BASE_DIR):
        for f in filenames:
            if f.endswith('.md'):
                files.append(os.path.join(root, f))
    return sorted(files)

def parse_frontmatter(content):
    if not content.startswith('---'):
        return {}, content
    parts = content.split('---', 2)
    if len(parts) < 3:
        return {}, content
    fm_text = parts[1].strip()
    body = parts[2].strip()
    fm = {}
    for line in fm_text.split('\n'):
        if ':' in line:
            key, val = line.split(':', 1)
            fm[key.strip()] = val.strip()
    return fm, body

def check_frontmatter(fm):
    missing = []
    for key in REQUIRED_FM_KEYS:
        if key not in fm:
            missing.append(key)
    return missing

def check_formal_definition(body):
    # 定义 X.X 或 Definition X.X
    pattern = re.compile(r'\*\*定义\s+\d+(\.\d+)*\*\*|\*\*Definition\s+\d+(\.\d+)*\*\*', re.IGNORECASE)
    return bool(pattern.search(body))

def check_theorem_proof(body):
    # 定理 X.X + 证明段落
    theorem_pattern = re.compile(r'\*\*定理\s+\d+(\.\d+)*\*\*|\*\*Theorem\s+\d+(\.\d+)*\*\*', re.IGNORECASE)
    has_theorem = bool(theorem_pattern.search(body))
    # 证明段落：包含"证明"关键词的段落
    proof_pattern = re.compile(r'(?:^|\n)\s*#{1,6}\s*.*证明|(?:^|\n)\s*>\s*\*\*证明\*\*|(?:^|\n)\s*\*\*证明', re.IGNORECASE)
    has_proof_section = bool(proof_pattern.search(body))
    return has_theorem, has_proof_section

def check_loop_invariant_induction(body):
    # 循环不变式或归纳证明
    inv_pattern = re.compile(r'循环不变式|loop\s+invariant|不变式', re.IGNORECASE)
    induction_pattern = re.compile(r'归纳证明|归纳法|数学归纳法|induction', re.IGNORECASE)
    return bool(inv_pattern.search(body)), bool(induction_pattern.search(body))

def check_mermaid(body):
    return len(re.findall(r'```mermaid', body))

def check_self_assessment(body):
    # 自测问题或 Self-Assessment 章节
    section_pattern = re.compile(r'#{1,6}\s*.*自测问题|#{1,6}\s*.*Self-Assessment', re.IGNORECASE)
    has_section = bool(section_pattern.search(body))
    if has_section:
        # 统计问题数量（Q: 或 问题 N:）
        q_count = len(re.findall(r'(?:^|\n)\s*(?:\*\*)?\s*(?:Q|问题)\s*\d*[:：]', body, re.IGNORECASE))
        # 另一种形式
        q_count2 = len(re.findall(r'#{1,6}\s*.*问题\s*\d+', body, re.IGNORECASE))
        return True, max(q_count, q_count2)
    return False, 0

def check_references(body):
    ref_section = re.compile(r'#{1,6}\s*.*参考文献|#{1,6}\s*.*References', re.IGNORECASE)
    has_section = bool(ref_section.search(body))
    if has_section:
        # 检查是否包含"待补充"
        # 提取参考文献章节内容
        match = ref_section.search(body)
        if match:
            start = match.start()
            # 找到下一个同级或更高级标题
            next_header = re.search(r'\n#{1,6}\s', body[start+1:])
            if next_header:
                ref_content = body[start:start+1+next_header.start()]
            else:
                ref_content = body[start:]
            if '待补充' in ref_content or 'TBD' in ref_content or 'TODO' in ref_content.upper():
                return True, True  # 有章节但有待补充标记
        return True, False
    return False, False

def check_learning_objectives(body):
    pattern = re.compile(r'#{1,6}\s*.*学习目标|#{1,6}\s*.*Learning\s+Objectives', re.IGNORECASE)
    return bool(pattern.search(body))

def classify_doc(filepath, body):
    """分类文档类型：导论、附录、算法类"""
    name = os.path.basename(filepath)
    if '导论' in name or 'Introduction' in name or '总览' in name:
        return 'intro'
    if '附录' in name or '索引' in name or '清单' in name or '模板' in name or '速查' in name:
        return 'appendix'
    return 'algorithm'

def main():
    files = get_all_md_files()
    total = len(files)
    print(f"=" * 80)
    print(f"LeetCode算法面试专题 - 形式化完整性质量审计报告")
    print(f"审计时间: {datetime.now().isoformat()}")
    print(f"文档总数: {total}")
    print(f"=" * 80)
    
    results = []
    stats = {
        'fm_pass': 0, 'definition_pass': 0, 'theorem_pass': 0, 'proof_pass': 0,
        'loop_inv_pass': 0, 'mermaid_pass': 0, 'self_assess_pass': 0,
        'ref_pass': 0, 'lo_pass': 0
    }
    
    for filepath in files:
        rel_path = os.path.relpath(filepath, BASE_DIR)
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        fm, body = parse_frontmatter(content)
        doc_type = classify_doc(filepath, body)
        
        # 1. Frontmatter
        fm_missing = check_frontmatter(fm)
        fm_ok = len(fm_missing) == 0
        
        # 2. 形式化定义
        has_def = check_formal_definition(body)
        
        # 3. 定理+证明
        has_theorem, has_proof = check_theorem_proof(body)
        
        # 4. 循环不变式/归纳法
        has_loop_inv, has_induction = check_loop_invariant_induction(body)
        has_loop_or_induction = has_loop_inv or has_induction
        
        # 5. Mermaid
        mermaid_count = check_mermaid(body)
        
        # 6. 自测问题
        has_sa, sa_count = check_self_assessment(body)
        
        # 7. 参考文献
        has_ref, ref_tbd = check_references(body)
        
        # 8. 学习目标
        has_lo = check_learning_objectives(body)
        
        # 统计
        if fm_ok: stats['fm_pass'] += 1
        if has_def: stats['definition_pass'] += 1
        if has_theorem: stats['theorem_pass'] += 1
        if has_proof: stats['proof_pass'] += 1
        if has_loop_or_induction: stats['loop_inv_pass'] += 1
        if mermaid_count >= 3: stats['mermaid_pass'] += 1
        if has_sa and sa_count >= 3: stats['self_assess_pass'] += 1
        if has_ref and not ref_tbd: stats['ref_pass'] += 1
        if has_lo: stats['lo_pass'] += 1
        
        # 判定总体状态
        issues = []
        if not fm_ok:
            issues.append(f"frontmatter缺失: {fm_missing}")
        if doc_type == 'algorithm':
            if not has_def:
                issues.append("无形式化定义")
            if not has_theorem:
                issues.append("无定理")
            if not has_proof:
                issues.append("无证明段落")
            if not has_loop_or_induction:
                issues.append("无循环不变式/归纳法")
        if mermaid_count < 3:
            issues.append(f"Mermaid不足({mermaid_count}<3)")
        if not has_sa:
            issues.append("无自测问题章节")
        elif sa_count < 3:
            issues.append(f"自测问题不足({sa_count}<3)")
        if not has_ref:
            issues.append("无参考文献章节")
        elif ref_tbd:
            issues.append("参考文献待补充")
        if not has_lo:
            issues.append("无学习目标")
        
        # 评分
        critical_missing = []
        if doc_type == 'algorithm':
            if not has_def:
                critical_missing.append("形式化定义")
            if not has_theorem or not has_proof:
                critical_missing.append("定理/证明")
        
        if critical_missing:
            status = "失败"
        elif issues:
            # 如果只有frontmatter小问题或mermaid差一点，算警告
            if all(i.startswith("frontmatter") or i.startswith("Mermaid") for i in issues):
                status = "警告"
            else:
                status = "警告"
        else:
            status = "通过"
        
        results.append({
            'path': rel_path,
            'type': doc_type,
            'status': status,
            'issues': issues,
            'critical': critical_missing,
            'fm_ok': fm_ok,
            'has_def': has_def,
            'has_theorem': has_theorem,
            'has_proof': has_proof,
            'has_loop_inv': has_loop_inv,
            'has_induction': has_induction,
            'mermaid_count': mermaid_count,
            'has_sa': has_sa,
            'sa_count': sa_count,
            'has_ref': has_ref,
            'ref_tbd': ref_tbd,
            'has_lo': has_lo,
        })
    
    # 输出每篇文档评分
    print("\n" + "=" * 80)
    print("一、逐文档质量评分")
    print("=" * 80)
    for r in results:
        icon = "✅" if r['status'] == "通过" else ("⚠️" if r['status'] == "警告" else "❌")
        print(f"{icon} [{r['status']}] {r['path']}")
        if r['issues']:
            for issue in r['issues']:
                print(f"   - {issue}")
    
    # 输出统计
    print("\n" + "=" * 80)
    print("二、整体统计")
    print("=" * 80)
    print(f"文档总数: {total}")
    print(f"通过: {sum(1 for r in results if r['status']=='通过')}  |  警告: {sum(1 for r in results if r['status']=='警告')}  |  失败: {sum(1 for r in results if r['status']=='失败')}")
    print()
    print("各维度通过率:")
    for key, label in [
        ('fm_pass', 'YAML frontmatter 完整性'),
        ('definition_pass', '形式化定义'),
        ('theorem_pass', '定理'),
        ('proof_pass', '证明段落'),
        ('loop_inv_pass', '循环不变式/归纳法'),
        ('mermaid_pass', 'Mermaid图表≥3'),
        ('self_assess_pass', '自测问题≥3'),
        ('ref_pass', '参考文献（非待补充）'),
        ('lo_pass', '学习目标'),
    ]:
        print(f"  {label}: {stats[key]}/{total} ({stats[key]*100//total}%)")
    
    # 严重缺失列表
    print("\n" + "=" * 80)
    print("三、严重缺失文档（需修复）")
    print("=" * 80)
    for r in results:
        if r['critical']:
            print(f"❌ {r['path']}")
            print(f"   严重缺失: {', '.join(r['critical'])}")
    
    # 返回数据供修复使用
    return results

if __name__ == '__main__':
    main()
