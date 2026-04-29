#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
update_module_owners.py

读取内容所有权分配表，批量更新对应模块下所有 Markdown 文件的 YAML frontmatter，
添加或更新 `owner` 字段。

用法:
    python scripts/update_module_owners.py --dry-run
    python scripts/update_module_owners.py --table docs/项目维护/内容所有权分配表_2026-04-29.md
"""

import argparse
import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    print("错误: 需要 PyYAML 包。请执行: pip install pyyaml", file=sys.stderr)
    sys.exit(1)


def parse_ownership_table(md_path: str) -> dict[str, str]:
    """
    解析 Markdown 表格，提取 模块/目录 -> 负责人 的映射。
    支持同一文件中有多个表格（如编号模块表 + 支持性目录表）。
    """
    mapping: dict[str, str] = {}
    with open(md_path, "r", encoding="utf-8") as f:
        content = f.read()

    in_table = False
    for line in content.splitlines():
        line_stripped = line.strip()
        # 检测到表头行则进入表格
        if "|" in line_stripped and "模块/目录" in line_stripped and "负责人" in line_stripped:
            in_table = True
            continue
        if not in_table:
            continue
        # 表格结束：遇到不以 | 开头的非空行
        if line_stripped and not line_stripped.startswith("|"):
            in_table = False
            continue
        # 跳过分隔行
        if line_stripped.startswith("|") and set(line_stripped.replace("|", "").strip()) <= {"-", ":", " ", ""}:
            continue
        if not line_stripped.startswith("|"):
            continue

        parts = [p.strip() for p in line_stripped.strip("|").split("|")]
        if len(parts) >= 2:
            module = parts[0]
            owner = parts[1]
            # 跳过表头重复行和空行
            if module and module != "模块/目录" and owner and owner != "负责人":
                mapping[module] = owner

    return mapping


def get_owner_for_path(rel_path: str, mapping: dict[str, str]) -> str | None:
    """
    根据文件相对路径，找到对应的负责人。
    优先匹配最长路径前缀。
    """
    posix_path = rel_path.replace(os.sep, "/")
    parts = posix_path.split("/")
    if not parts:
        return None

    # 从长到短尝试前缀匹配
    for i in range(len(parts), 0, -1):
        prefix = "/".join(parts[:i])
        for module, owner in mapping.items():
            if prefix == module or prefix.startswith(module + "/"):
                return owner

    return None


def parse_frontmatter(content: str) -> tuple[dict | None, str]:
    """
    解析 YAML frontmatter。返回 (frontmatter_dict, body)。
    如果没有 frontmatter，返回 (None, content)。
    """
    if not content.startswith("---"):
        return None, content

    # 匹配 ---\n...---\n 或 ---\r\n...\r\n---\r\n
    match = re.match(r"^---\s*(?:\n|\r\n)(.*?)(?:\n|\r\n)---\s*(?:\n|\r\n|$)", content, re.DOTALL)
    if not match:
        return None, content

    try:
        fm = yaml.safe_load(match.group(1))
        if not isinstance(fm, dict):
            fm = {}
    except yaml.YAMLError as e:
        print(f"警告: YAML 解析失败，跳过 frontmatter: {e}")
        return None, content

    body = content[match.end():]
    return fm, body


def update_frontmatter(content: str, owner: str) -> tuple[str, bool, bool]:
    """
    更新 frontmatter 中的 owner 字段。
    返回: (新内容, 是否已修改, 是否保留原值)
    """
    fm, body = parse_frontmatter(content)

    if fm is None:
        # 没有 frontmatter，创建新的
        new_fm = {"owner": owner}
        fm_yaml = yaml.safe_dump(new_fm, allow_unicode=True, sort_keys=False)
        new_content = f"---\n{fm_yaml}---\n\n{body}"
        return new_content, True, False

    existing_owner = fm.get("owner")
    if existing_owner is not None and str(existing_owner).strip():
        # 已有 owner 且不为空，保留原值
        return content, False, True

    fm["owner"] = owner
    fm_yaml = yaml.safe_dump(fm, allow_unicode=True, sort_keys=False)
    new_content = f"---\n{fm_yaml}---\n\n{body}"
    return new_content, True, False


def main() -> int:
    parser = argparse.ArgumentParser(
        description="批量更新 Markdown 文件的 owner 字段",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python scripts/update_module_owners.py --dry-run
  python scripts/update_module_owners.py --table docs/项目维护/内容所有权分配表_2026-04-29.md
        """,
    )
    parser.add_argument(
        "--table",
        default="docs/项目维护/内容所有权分配表_2026-04-29.md",
        help="内容所有权分配表路径 (默认: docs/项目维护/内容所有权分配表_2026-04-29.md)",
    )
    parser.add_argument(
        "--docs-dir",
        default="docs",
        help="文档根目录 (默认: docs)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="预览变更，不实际写入文件",
    )
    args = parser.parse_args()

    if not os.path.exists(args.table):
        print(f"错误: 所有权分配表不存在: {args.table}", file=sys.stderr)
        return 1

    mapping = parse_ownership_table(args.table)
    if not mapping:
        print("错误: 未能从表格中解析出任何映射关系", file=sys.stderr)
        return 1

    print(f"已加载 {len(mapping)} 条模块所有权映射")
    print("映射预览:")
    for module, owner in sorted(mapping.items()):
        print(f"  {module:<35} -> {owner}")
    print()

    docs_path = Path(args.docs_dir)
    if not docs_path.exists():
        print(f"错误: 文档目录不存在: {docs_path}", file=sys.stderr)
        return 1

    stats = {
        "scanned": 0,
        "processed": 0,
        "updated": 0,
        "preserved": 0,
        "no_mapping": 0,
        "yaml_error": 0,
    }

    for md_file in sorted(docs_path.rglob("*.md")):
        rel_path = md_file.relative_to(docs_path).as_posix()
        stats["scanned"] += 1
        owner = get_owner_for_path(rel_path, mapping)

        if not owner:
            stats["no_mapping"] += 1
            continue

        stats["processed"] += 1
        try:
            content = md_file.read_text(encoding="utf-8")
        except Exception as e:
            print(f"[错误] 无法读取 {rel_path}: {e}")
            continue

        try:
            new_content, modified, preserved = update_frontmatter(content, owner)
        except Exception as e:
            print(f"[错误] 处理 frontmatter 失败 {rel_path}: {e}")
            stats["yaml_error"] += 1
            continue

        if preserved:
            stats["preserved"] += 1
            existing_fm, _ = parse_frontmatter(content)
            existing_owner = existing_fm.get("owner") if existing_fm else None
            print(f"[保留] {rel_path} (现有 owner: {existing_owner})")
        elif modified:
            stats["updated"] += 1
            print(f"[更新] {rel_path} -> owner: {owner}")
            if not args.dry_run:
                md_file.write_text(new_content, encoding="utf-8")

    print("\n--- 统计 ---")
    print(f"扫描文件数: {stats['scanned']}")
    print(f"匹配映射:   {stats['processed']}")
    print(f"  已更新:   {stats['updated']}")
    print(f"  保留原值: {stats['preserved']}")
    print(f"无映射:     {stats['no_mapping']}")
    if stats["yaml_error"]:
        print(f"YAML 错误:  {stats['yaml_error']}")

    if args.dry_run:
        print("\n(当前为 --dry-run 预览模式，未实际写入文件)")

    return 0


if __name__ == "__main__":
    sys.exit(main())
