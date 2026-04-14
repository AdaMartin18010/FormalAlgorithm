#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
季度内容审查脚本 / Quarterly Content Review Script

功能：
1. 扫描 docs/ 下所有 .md 文件，提取 last_updated 或文档顶部日期
2. 列出超过 365 天未更新的文档
3. 读取 docs/references_database_2024_2025.yaml，检查哪些引用未被任何 .md 文件引用
4. 输出审查报告到 reports/quarterly_review_YYYY-MM-DD.md
"""

import os
import re
import sys
from datetime import datetime, timedelta
from pathlib import Path

DOCS_DIR = Path("docs")
REFS_FILE = Path("docs/references_database_2024_2025.yaml")
REPORTS_DIR = Path("reports")
TODAY = datetime.now()
CUTOFF = TODAY - timedelta(days=365)


def extract_last_updated(file_path: Path) -> datetime | None:
    """从 YAML frontmatter 或文档顶部提取最后更新日期"""
    try:
        text = file_path.read_text(encoding="utf-8")
    except Exception:
        return None

    # 1. 尝试 YAML frontmatter
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            frontmatter = text[3:end]
            m = re.search(r'last_updated:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})', frontmatter)
            if m:
                try:
                    return datetime.strptime(m.group(1), "%Y-%m-%d")
                except ValueError:
                    pass

    # 2. 尝试文档顶部 20 行中的日期模式
    lines = text.splitlines()[:20]
    for line in lines:
        # 匹配 **最后更新**: 2025-01-11 或 创建日期: 2025-01-11
        m = re.search(r'(?:最后更新|创建日期|更新日期|日期):\s*([0-9]{4}-[0-9]{2}-[0-9]{2})', line)
        if m:
            try:
                return datetime.strptime(m.group(1), "%Y-%m-%d")
            except ValueError:
                pass
        # 匹配 > **最后更新**: 2025-01-11
        m = re.search(r'([0-9]{4}-[0-9]{2}-[0-9]{2})', line)
        if m:
            try:
                dt = datetime.strptime(m.group(1), "%Y-%m-%d")
                # 只接受 2000-2099 的日期
                if 2000 <= dt.year <= 2099:
                    return dt
            except ValueError:
                pass

    # 3. 使用文件修改时间作为后备
    try:
        mtime = file_path.stat().st_mtime
        return datetime.fromtimestamp(mtime)
    except Exception:
        return None


def scan_docs() -> list[dict]:
    """扫描所有 .md 文件并返回过期文档列表"""
    stale_docs = []
    for root, _, files in os.walk(DOCS_DIR):
        for f in files:
            if not f.endswith(".md"):
                continue
            path = Path(root) / f
            updated = extract_last_updated(path)
            if updated and updated < CUTOFF:
                stale_docs.append({
                    "path": str(path.relative_to(".")),
                    "last_updated": updated.strftime("%Y-%m-%d"),
                    "days_ago": (TODAY - updated).days,
                })
    # 按天数降序排列
    stale_docs.sort(key=lambda x: x["days_ago"], reverse=True)
    return stale_docs


def extract_reference_keys() -> set[str]:
    """从引用数据库中提取引用标签（如 [AuthorYear] 或 AuthorYear）"""
    keys = set()
    if not REFS_FILE.exists():
        return keys

    text = REFS_FILE.read_text(encoding="utf-8")
    # 匹配常见的引用键格式：
    # - id: "Knuth1973"
    # - key: "Cormen2022"
    # 或者直接 [AuthorYear] 格式的行
    for m in re.finditer(r'[\-\s]*(?:id|key|citation_key):\s*"?([^"\n]+)"?', text):
        key = m.group(1).strip()
        if key:
            keys.add(key)
    # 也匹配文中出现的 [AuthorYear] 格式
    for m in re.finditer(r'\[([A-Z][a-zA-Z]+\d{4}[a-z]?)\]', text):
        keys.add(m.group(1))
    return keys


def find_uncited_references(keys: set[str]) -> list[str]:
    """检查哪些引用键未被任何 .md 文件引用"""
    if not keys:
        return []

    uncited = []
    # 为了提高效率，先读取所有 .md 内容拼接成一个大字符串
    all_md_text = ""
    for root, _, files in os.walk(DOCS_DIR):
        for f in files:
            if f.endswith(".md"):
                try:
                    all_md_text += (Path(root) / f).read_text(encoding="utf-8")
                except Exception:
                    pass

    for key in sorted(keys):
        # 支持多种引用格式： [Knuth1973]、Knuth1973、Knuth 1973
        pattern = re.compile(rf"\b{re.escape(key)}\b")
        if not pattern.search(all_md_text):
            uncited.append(key)
    return uncited


def generate_report(stale_docs: list[dict], uncited_refs: list[str]) -> Path:
    """生成季度审查报告"""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    report_path = REPORTS_DIR / f"quarterly_review_{TODAY.strftime('%Y-%m-%d')}.md"

    lines = [
        f"# 季度内容审查报告 / Quarterly Content Review Report",
        "",
        f"- **生成日期**: {TODAY.strftime('%Y-%m-%d')}",
        f"- **审查阈值**: 超过 {CUTOFF.strftime('%Y-%m-%d')} 未更新的文档",
        f"- **扫描范围**: `{DOCS_DIR}/` 下所有 `.md` 文件",
        "",
        "---",
        "",
        "## 1. 文档时效性检查 / Document Timeliness",
        "",
        f"共发现 **{len(stale_docs)}** 个文档超过 365 天未更新。",
        "",
    ]

    if stale_docs:
        lines.append("| 文档路径 | 最后更新日期 | 距今天数 |")
        lines.append("|---------|------------|---------|")
        for doc in stale_docs:
            lines.append(f"| {doc['path']} | {doc['last_updated']} | {doc['days_ago']} |")
    else:
        lines.append("✅ 所有文档均在 365 天内更新过。")

    lines.extend([
        "",
        "---",
        "",
        "## 2. 引用数据库检查 / Reference Database Check",
        "",
        f"引用数据库: `{REFS_FILE}`",
        "",
    ])

    if uncited_refs:
        lines.append(f"共发现 **{len(uncited_refs)}** 条引用未被任何 `.md` 文件引用。")
        lines.append("")
        lines.append("| 未引用条目 |")
        lines.append("|-----------|")
        for ref in uncited_refs[:100]:  # 最多显示 100 条
            lines.append(f"| {ref} |")
        if len(uncited_refs) > 100:
            lines.append(f"| ... 还有 {len(uncited_refs) - 100} 条未列出 |")
    else:
        lines.append("✅ 引用数据库中的所有条目均已被至少一个文档引用。")

    lines.extend([
        "",
        "---",
        "",
        "## 3. 后续建议 / Recommendations",
        "",
        "1. 对过期文档按模块优先级分配更新负责人。",
        "2. 对未引用文献评估其价值：删除冗余条目或补充到相关文档中。",
        "3. 运行代码示例编译检查（`cargo test`、`lake build`、`pytest` 等）。",
        "4. 核对 Wiki 对齐表与外部链接有效性。",
        "",
        "---",
        "",
        "*本报告由 `scripts/quarterly_review.py` 自动生成。*",
        "",
    ])

    report_path.write_text("\n".join(lines), encoding="utf-8")
    return report_path


def main():
    print("=== 开始季度内容审查 ===")
    print(f"当前日期: {TODAY.strftime('%Y-%m-%d')}")
    print(f"过期阈值: {CUTOFF.strftime('%Y-%m-%d')}")
    print()

    print("[1/3] 扫描文档更新日期...")
    stale_docs = scan_docs()
    print(f"      发现 {len(stale_docs)} 个过期文档")

    print("[2/3] 检查引用数据库...")
    ref_keys = extract_reference_keys()
    print(f"      从 {REFS_FILE} 提取到 {len(ref_keys)} 条引用键")
    uncited_refs = find_uncited_references(ref_keys)
    print(f"      发现 {len(uncited_refs)} 条未引用条目")

    print("[3/3] 生成审查报告...")
    report_path = generate_report(stale_docs, uncited_refs)
    print(f"      报告已保存至: {report_path}")

    print()
    print("=== 审查完成 ===")


if __name__ == "__main__":
    main()
