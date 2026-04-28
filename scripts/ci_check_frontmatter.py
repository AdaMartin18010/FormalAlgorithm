#!/usr/bin/env python3
"""
CI 脚本：检查 docs/ 目录下 Markdown 文件的 YAML frontmatter 完整性。

要求字段：title, version, status, last_updated

用法:
    python scripts/ci_check_frontmatter.py [docs_dir]
    python scripts/ci_check_frontmatter.py --strict [docs_dir]

退出码:
    0 - 所有检查通过（或仅在非 strict 模式下缺少 frontmatter）
    1 - 存在 frontmatter 但不完整，或 strict 模式下存在缺少 frontmatter 的文件
"""

import argparse
import os
import re
import sys

# 匹配 YAML frontmatter: --- ... ---
YAML_FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*\n", re.DOTALL)

# 提取 YAML 键名（简单实现，适用于项目中的单行 frontmatter）
YAML_KEY_RE = re.compile(r"^([\w_]+)\s*:", re.MULTILINE)

REQUIRED_FIELDS = {"title", "version", "status", "last_updated"}


def check_frontmatter(file_path: str) -> tuple[bool, set[str] | None]:
    """
    返回: (has_frontmatter, missing_fields)
    - has_frontmatter: 文件是否包含 YAML frontmatter
    - missing_fields: 缺失的必需字段集合，None 表示没有 frontmatter
    """
    with open(file_path, "r", encoding="utf-8") as f:
        # 只读取前 4KB，frontmatter 不会更长
        content = f.read(4096)

    match = YAML_FRONTMATTER_RE.match(content)
    if not match:
        return False, None

    yaml_text = match.group(1)
    present_keys = set(YAML_KEY_RE.findall(yaml_text))
    missing = REQUIRED_FIELDS - present_keys
    return True, missing


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Markdown frontmatter completeness under docs/"
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Also fail on files completely missing frontmatter",
    )
    parser.add_argument(
        "docs_dir",
        nargs="?",
        default="docs",
        help="Directory to scan for Markdown files (default: docs)",
    )
    args = parser.parse_args()

    docs_dir = args.docs_dir
    if not os.path.isdir(docs_dir):
        print(f"ERROR: Directory '{docs_dir}' does not exist", file=sys.stderr)
        return 1

    total = 0
    passed = 0
    incomplete_records = []
    missing_records = []

    for root, _, filenames in os.walk(docs_dir):
        for filename in filenames:
            if not filename.endswith(".md"):
                continue
            total += 1
            file_path = os.path.join(root, filename)
            has_fm, missing_fields = check_frontmatter(file_path)

            if not has_fm:
                missing_records.append(file_path)
            elif missing_fields:
                incomplete_records.append((file_path, missing_fields))
            else:
                passed += 1

    # 输出报告
    print("=" * 70)
    print("Markdown Frontmatter Check Report")
    print("=" * 70)
    print(f"Docs directory   : {docs_dir}")
    print(f"Total files      : {total}")
    print(f"Passed           : {passed}")
    print(f"Incomplete FM    : {len(incomplete_records)}")
    print(f"Missing FM       : {len(missing_records)}")
    print("-" * 70)

    if incomplete_records:
        print("\n❌ Files with INCOMPLETE frontmatter (missing required fields):")
        for path, fields in sorted(incomplete_records):
            rel = os.path.relpath(path, docs_dir)
            print(f"   - {rel}")
            print(f"     missing: {', '.join(sorted(fields))}")

    if missing_records:
        print("\n⚠️  Files MISSING frontmatter entirely:")
        for path in sorted(missing_records):
            rel = os.path.relpath(path, docs_dir)
            print(f"   - {rel}")

    print("-" * 70)

    # 决定退出码
    exit_code = 0

    if incomplete_records:
        print(
            f"\nRESULT: FAIL  ({len(incomplete_records)} files have incomplete frontmatter)"
        )
        exit_code = 1
    else:
        print("\nRESULT: PASS  (no incomplete frontmatter)")

    if missing_records:
        if args.strict:
            print(
                f"RESULT: FAIL  ({len(missing_records)} files missing frontmatter in strict mode)"
            )
            exit_code = 1
        else:
            print(
                f"WARNING: {len(missing_records)} files missing frontmatter "
                f"(not failing in non-strict mode)"
            )

    # 覆盖率统计
    if total > 0:
        coverage = (passed / total) * 100
        print(f"\nFrontmatter coverage: {passed}/{total} ({coverage:.1f}%)")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
