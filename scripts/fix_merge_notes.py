#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复合并说明中的错误引用
"""

from pathlib import Path

PAIRS = [
    (
        "docs/05-类型理论/03-同伦类型论.md",
        "05-类型理论/03-同伦类型论.md",
        "05-类型理论/03-同伦类型论-高级深化.md",
    ),
    (
        "docs/07-计算模型/05-量子计算模型.md",
        "07-计算模型/05-量子计算模型.md",
        "07-计算模型/05-量子计算模型-高级深化.md",
    ),
    (
        "docs/08-实现示例/04-形式化验证.md",
        "08-实现示例/04-形式化验证.md",
        "08-实现示例/04-形式化验证-高级深化.md",
    ),
    (
        "docs/09-算法理论/01-算法基础/17-神经网络算法理论.md",
        "09-算法理论/01-算法基础/17-神经网络算法理论.md",
        "09-算法理论/01-算法基础/17-神经网络算法理论-高级深化.md",
    ),
    (
        "docs/10-高级主题/30-边缘计算中的算法系统.md",
        "10-高级主题/30-边缘计算中的算法系统.md",
        "10-高级主题/30-边缘计算中的算法系统-高级深化.md",
    ),
    (
        "docs/10-高级主题/33-算法在生物计算中的应用.md",
        "10-高级主题/33-算法在生物计算中的应用.md",
        "10-高级主题/33-算法在生物计算中的应用-高级深化.md",
    ),
    (
        "docs/10-高级主题/34-算法在脑机接口中的应用.md",
        "10-高级主题/34-算法在脑机接口中的应用.md",
        "10-高级主题/34-算法在脑机接口中的应用-高级深化.md",
    ),
    (
        "docs/12-应用领域/02-区块链算法应用.md",
        "12-应用领域/02-区块链算法应用.md",
        "12-应用领域/02-区块链算法应用-高级深化.md",
    ),
]

for base_path, base_name, adv_name in PAIRS:
    path = Path(base_path)
    if not path.exists():
        continue
    content = path.read_text(encoding="utf-8")
    old = f"> **合并说明**: 本文档由原 `{base_name}` 和 `{base_name}` 合并而成，整合时间: 2026-04-15"
    new = f"> **合并说明**: 本文档由原 `{base_name}` 和 `{adv_name}` 合并而成，整合时间: 2026-04-15"
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        print(f"[FIXED] {base_path}")
    else:
        print(f"[SKIP ] {base_path} (pattern not found)")
