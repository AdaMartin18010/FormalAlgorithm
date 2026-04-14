#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
文档合并脚本：将8对高级深化版本文档合并到基础版本中
"""

import os
import re
from pathlib import Path

# 定义8对文档
PAIRS = [
    (
        "docs/05-类型理论/03-同伦类型论.md",
        "docs/05-类型理论/03-同伦类型论-高级深化.md",
        "03-同伦类型论-高级深化.md",
    ),
    (
        "docs/07-计算模型/05-量子计算模型.md",
        "docs/07-计算模型/05-量子计算模型-高级深化.md",
        "05-量子计算模型-高级深化.md",
    ),
    (
        "docs/08-实现示例/04-形式化验证.md",
        "docs/08-实现示例/04-形式化验证-高级深化.md",
        "04-形式化验证-高级深化.md",
    ),
    (
        "docs/09-算法理论/01-算法基础/17-神经网络算法理论.md",
        "docs/09-算法理论/01-算法基础/17-神经网络算法理论-高级深化.md",
        "17-神经网络算法理论-高级深化.md",
    ),
    (
        "docs/10-高级主题/30-边缘计算中的算法系统.md",
        "docs/10-高级主题/30-边缘计算中的算法系统-高级深化.md",
        "30-边缘计算中的算法系统-高级深化.md",
    ),
    (
        "docs/10-高级主题/33-算法在生物计算中的应用.md",
        "docs/10-高级主题/33-算法在生物计算中的应用-高级深化.md",
        "33-算法在生物计算中的应用-高级深化.md",
    ),
    (
        "docs/10-高级主题/34-算法在脑机接口中的应用.md",
        "docs/10-高级主题/34-算法在脑机接口中的应用-高级深化.md",
        "34-算法在脑机接口中的应用-高级深化.md",
    ),
    (
        "docs/12-应用领域/02-区块链算法应用.md",
        "docs/12-应用领域/02-区块链算法应用-高级深化.md",
        "02-区块链算法应用-高级深化.md",
    ),
]


def strip_frontmatter(content: str) -> str:
    """移除YAML frontmatter"""
    if content.startswith("---"):
        idx = content.find("---", 3)
        if idx != -1:
            return content[idx + 3 :].lstrip("\n")
    return content


def strip_main_title(content: str) -> str:
    """移除文档的第一个主标题（# 或 ## 开头的标题行）"""
    lines = content.splitlines()
    result = []
    title_removed = False
    for line in lines:
        if not title_removed and (line.startswith("# ") or line.startswith("## ")):
            title_removed = True
            continue
        result.append(line)
    return "\n".join(result).lstrip("\n")


def merge_pair(base_path: str, adv_path: str, adv_basename: str):
    """将advanced内容合并到base文档中"""
    base_full = Path(base_path)
    adv_full = Path(adv_path)

    if not base_full.exists():
        print(f"[WARN] 基础文档不存在: {base_path}，将高级文档重命名为基础文档")
        # 直接重命名，并清理标题
        content = adv_full.read_text(encoding="utf-8")
        content = strip_frontmatter(content)
        content = strip_main_title(content)
        # 重新添加标准frontmatter
        new_title = "10.34 算法在脑机接口中的应用 / Algorithms in Brain-Computer Interface"
        new_frontmatter = f"---\ntitle: {new_title}\nversion: 1.0\nstatus: maintained\nlast_updated: 2025-01-11\nowner: 高级主题工作组\n---\n\n"
        note = f"> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../项目全面梳理-2025.md)\n\n"
        final_content = new_frontmatter + note + "## 10.34 算法在脑机接口中的应用 / Algorithms in Brain-Computer Interface\n\n" + content
        base_full.write_text(final_content, encoding="utf-8")
        adv_full.unlink()
        print(f"[DONE] 重命名 {adv_path} -> {base_path}")
        return

    base_content = base_full.read_text(encoding="utf-8")
    adv_content = adv_full.read_text(encoding="utf-8")

    # 处理高级文档
    adv_content = strip_frontmatter(adv_content)
    adv_content = strip_main_title(adv_content)

    # 构建追加内容
    append_section = f"\n\n---\n\n<details>\n<summary><h2>高级深化内容</h2></summary>\n\n{adv_content}\n\n</details>\n"

    # 更新或添加合并说明
    merge_note = f"> **合并说明**: 本文档由原 `{base_path.replace('docs/', '')}` 和 `{adv_path.replace('docs/', '')}` 合并而成，整合时间: 2026-04-15\n"
    if "**合并说明**:" in base_content:
        base_content = re.sub(r"> \*\*合并说明\*\*:.*\n", merge_note, base_content)
    else:
        # 在第一个引用块之后或文档开头添加
        lines = base_content.splitlines()
        inserted = False
        for i, line in enumerate(lines):
            if line.startswith("> ") and i + 1 < len(lines) and not lines[i + 1].startswith("> "):
                lines.insert(i + 1, merge_note.rstrip())
                inserted = True
                break
        if not inserted:
            # 在frontmatter后插入
            if lines[0] == "---":
                idx = 0
                for i, line in enumerate(lines[1:], 1):
                    if line == "---":
                        idx = i
                        break
                lines.insert(idx + 1, merge_note.rstrip())
            else:
                lines.insert(0, merge_note.rstrip())
        base_content = "\n".join(lines)

    # 追加高级内容
    base_content = base_content.rstrip() + append_section

    base_full.write_text(base_content, encoding="utf-8")
    adv_full.unlink()
    print(f"[DONE] 合并 {adv_path} -> {base_path}")


def update_links():
    """更新所有指向已删除高级文档的链接"""
    replacements = {
        "03-同伦类型论-高级深化.md": "03-同伦类型论.md",
        "05-量子计算模型-高级深化.md": "05-量子计算模型.md",
        "04-形式化验证-高级深化.md": "04-形式化验证.md",
        "17-神经网络算法理论-高级深化.md": "17-神经网络算法理论.md",
        "30-边缘计算中的算法系统-高级深化.md": "30-边缘计算中的算法系统.md",
        "33-算法在生物计算中的应用-高级深化.md": "33-算法在生物计算中的应用.md",
        "34-算法在脑机接口中的应用-高级深化.md": "34-算法在脑机接口中的应用.md",
        "02-区块链算法应用-高级深化.md": "02-区块链算法应用.md",
    }

    updated_files = []
    for root, _, files in os.walk("docs"):
        for file in files:
            if not file.endswith(".md"):
                continue
            path = Path(root) / file
            content = path.read_text(encoding="utf-8")
            original = content
            for old, new in replacements.items():
                content = content.replace(old, new)
            if content != original:
                path.write_text(content, encoding="utf-8")
                updated_files.append(str(path))
                print(f"[LINK] 更新链接: {path}")

    return updated_files


def main():
    print("=== 开始文档合并 ===")
    for base_path, adv_path, adv_basename in PAIRS:
        merge_pair(base_path, adv_path, adv_basename)

    print("\n=== 开始更新内部链接 ===")
    updated = update_links()

    print(f"\n=== 完成 ===")
    print(f"合并文档对数: {len(PAIRS)}")
    print(f"更新链接文件数: {len(updated)}")


if __name__ == "__main__":
    main()
