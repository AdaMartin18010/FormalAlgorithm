#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
convert_refs_to_bibtex.py

功能：读取项目现有的 YAML 引用数据库，转换为标准 BibTeX (.bib) 文件。
支持从以下源读取：
  - docs/references_database_2024_2025.yaml
  - docs/引用规范与数据库.md（提取内嵌 YAML 块）

输出：docs/references.bib

用法：
    python scripts/convert_refs_to_bibtex.py

作者：项目维护团队
创建日期：2026-04-29
"""

import re
import sys
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError:
    print("错误：需要 PyYAML。请运行: pip install pyyaml")
    sys.exit(1)

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = PROJECT_ROOT / "docs"
OUTPUT_BIB = DOCS_DIR / "references.bib"

# YAML type -> BibTeX entry type 映射
ENTRY_TYPE_MAP = {
    "book": "book",
    "textbook": "book",
    "paper": "article",          # 需要根据 venue 进一步推断
    "journal_article": "article",
    "conference_paper": "inproceedings",
    "book_chapter": "incollection",
    "thesis": "phdthesis",       # 默认博士，特殊情况需覆盖
    "technical_report": "misc",
    "preprint": "misc",
    "online": "misc",
    "course": "misc",
    "software_release": "misc",
    "software_library": "misc",
    "tutorial": "misc",
    "competition": "misc",
}

# venue 关键词 -> entry type 推断（当 type 为 paper 或 venue 不明确时）
CONFERENCE_HINTS = [
    "proceedings", "conference", "symposium", "workshop",
    "stoc", "focs", "soda", "icalp", "cav", "cpp", "popl",
    "icml", "neurips", "iclr", "aaai", "ijcai",
]
JOURNAL_HINTS = [
    "journal", "transactions", "letters", "review",
    "nature", "science", "acm", "ieee", "springer",
    "computational", "mathematical structures",
    "proceedings of the",  # Proceedings of the London Mathematical Society 是期刊
    "mathematical society", "american journal", "annals of",
]


def infer_entry_type(record: dict) -> str:
    """基于 YAML 字段推断 BibTeX entry type。"""
    raw_type = record.get("type", "").lower().strip()
    if raw_type in ENTRY_TYPE_MAP:
        mapped = ENTRY_TYPE_MAP[raw_type]
        # 对于 paper，需要根据 venue 进一步区分 article / inproceedings
        if mapped == "article" and raw_type == "paper":
            return _disambiguate_by_venue(record.get("venue", ""))
        return mapped
    # 如果没有 type 字段，尝试根据 venue 推断
    return _disambiguate_by_venue(record.get("venue", ""))


def _disambiguate_by_venue(venue: str) -> str:
    v = venue.lower()
    # 先检查明确的期刊模式（优先级高于会议关键词）
    journal_patterns = [
        "proceedings of the london mathematical society",
        "proceedings of the royal society",
        "proceedings of the national academy",
        "american journal of mathematics",
        "journal of the acm",
        "mathematical structures in computer science",
        "physical review letters",
        "physical review x",
        "nature",
        "science",
        "computational optimization and applications",
    ]
    for pat in journal_patterns:
        if pat in v:
            return "article"
    for hint in CONFERENCE_HINTS:
        if hint in v:
            return "inproceedings"
    for hint in JOURNAL_HINTS:
        if hint in v:
            return "article"
    # 如果有 booktitle 字样，视为会议/书籍章节
    if "booktitle" in v:
        return "incollection"
    # 默认 fallback
    return "misc"


def escape_bibtex_value(value: str) -> str:
    """对 BibTeX 字符串值进行基本转义。"""
    if not isinstance(value, str):
        value = str(value)
    # 保护已转义的 LaTeX 命令（简单启发式：如果已有反斜杠+字母，不重复转义）
    # 但需要对纯文本中的特殊字符进行保护
    # 策略：将值整体用大括号包裹，内部只处理必须转义的字符
    # BibTeX 中需要转义的特殊字符: # $ % & ~ _ ^ \ { }
    # 简单做法：如果字符串不含已知的 LaTeX 命令，则整体包裹
    # 这里采用保守策略：保护常见情况
    replacements = {
        "&": "\\&",
        "%": "\\%",
        "#": "\\#",
    }
    # 注意：不转义 $ _ ^ ~ \ { }，因为它们可能是合法的 LaTeX 命令或需要保留
    # 如果值中这些字符不是 LaTeX 意图，应在 YAML 中预先处理
    for old, new in replacements.items():
        value = value.replace(old, new)
    return value


def format_author(authors: list[str] | str) -> str:
    """将作者列表格式化为 BibTeX 的 'and' 连接形式。"""
    if isinstance(authors, str):
        return authors
    if isinstance(authors, list):
        return " and ".join(str(a).strip() for a in authors)
    return str(authors)


def extract_title(record: dict) -> str:
    """提取标题，优先英文标题。"""
    title = record.get("title")
    if isinstance(title, dict):
        # 优先 en，其次 zh
        return title.get("en") or title.get("zh") or ""
    if isinstance(title, str):
        return title
    return ""


def build_bibtex_entry(record: dict) -> str | None:
    """将单条 YAML 记录转换为 BibTeX 条目字符串。"""
    key = record.get("id") or record.get("reference_id")
    if not key:
        return None

    entry_type = infer_entry_type(record)
    lines = [f"@{entry_type}{{{key},"]

    # author
    authors = record.get("authors")
    if authors:
        lines.append(f"  author    = {{{format_author(authors)}}},")

    # title
    title = extract_title(record)
    if title:
        lines.append(f"  title     = {{{escape_bibtex_value(title)}}},")

    # venue -> journal / booktitle / publisher / school / howpublished
    venue = record.get("venue", "")
    institution = record.get("institution", "")
    raw_type = record.get("type", "").lower()

    if entry_type == "article":
        lines.append(f"  journal   = {{{escape_bibtex_value(venue)}}},")
    elif entry_type == "inproceedings":
        lines.append(f"  booktitle = {{{escape_bibtex_value(venue)}}},")
    elif entry_type == "book":
        lines.append(f"  publisher = {{{escape_bibtex_value(venue)}}},")
    elif entry_type == "phdthesis":
        lines.append(f"  school    = {{{escape_bibtex_value(institution or venue)}}},")
    elif entry_type in ("misc", "incollection"):
        # 对于 course / online 等，使用 howpublished 或 note
        if raw_type in ("course", "tutorial", "online") and (institution or venue):
            lines.append(f"  howpublished = {{{escape_bibtex_value(institution or venue)}}},")
        elif venue:
            lines.append(f"  howpublished = {{{escape_bibtex_value(venue)}}},")

    # year
    year = record.get("year")
    if year:
        lines.append(f"  year      = {{{year}}},")

    # month
    month = record.get("month")
    if month:
        lines.append(f"  month     = {{{month}}},")

    # pages
    pages = record.get("pages")
    if pages:
        lines.append(f"  pages     = {{{pages}}},")

    # doi
    doi = record.get("doi")
    if doi:
        lines.append(f"  doi       = {{{doi}}},")

    # url
    url = record.get("url")
    if url:
        lines.append(f"  url       = {{{url}}},")

    # isbn
    isbn = record.get("isbn")
    if isbn:
        lines.append(f"  isbn      = {{{isbn}}},")

    # arxiv -> eprint / note
    arxiv = record.get("arxiv")
    if arxiv:
        lines.append(f"  eprint    = {{{arxiv}}},")
        lines.append(f"  archivePrefix = {{arXiv}},")

    # edition (for books)
    edition = record.get("edition")
    if edition:
        lines.append(f"  edition   = {{{edition}}},")

    # volume / number (if present)
    volume = record.get("volume")
    if volume:
        lines.append(f"  volume    = {{{volume}}},")
    number = record.get("number")
    if number:
        lines.append(f"  number    = {{{number}}},")

    # note (summary, status, etc.)
    notes = []
    summary = record.get("summary")
    if summary:
        notes.append(summary)
    status = record.get("status")
    if status:
        notes.append(f"Status: {status}")
    award = record.get("award")
    if award:
        notes.append(f"Award: {award}")
    if notes:
        note_text = " ".join(notes)
        lines.append(f"  note      = {{{escape_bibtex_value(note_text)}}},")

    # 去掉最后一个逗号
    if lines and lines[-1].endswith(","):
        lines[-1] = lines[-1][:-1]

    lines.append("}")
    return "\n".join(lines)


def parse_yaml_file(filepath: Path) -> list[dict]:
    """解析独立 YAML 文件，返回记录列表。"""
    if not filepath.exists():
        print(f"警告：文件不存在 {filepath}")
        return []
    with open(filepath, "r", encoding="utf-8") as f:
        data = yaml.safe_load(f)
    if not data:
        return []

    records = []
    # 处理 category-based 结构（如 references_database_2024_2025.yaml）
    if isinstance(data, dict):
        for key, value in data.items():
            if key in ("metadata",):
                continue
            if isinstance(value, list):
                records.extend(value)
    elif isinstance(data, list):
        records.extend(data)
    return records


def _is_template_record(record: dict) -> bool:
    """判断是否为文档中的示例/模板记录。"""
    key = record.get("id") or record.get("reference_id", "")
    title = extract_title(record)
    # 排除明显的模板文字
    template_markers = [
        "唯一标识符", "作者列表", "标题 (中英文)", "出版物/会议/课程",
        "reference_id:", "[作者]", "[标题]", "[会议/期刊名称]",
    ]
    for marker in template_markers:
        if marker in str(key) or marker in str(title):
            return True
    # 如果作者字段为列表且包含模板文字
    authors = record.get("authors", [])
    if isinstance(authors, list):
        for a in authors:
            if any(m in str(a) for m in ["作者", "[作者]", "列表"]):
                return True
    return False


def parse_embedded_yaml_in_markdown(filepath: Path) -> list[dict]:
    """从 Markdown 文件中提取 ```yaml 代码块并解析为记录列表。"""
    if not filepath.exists():
        return []
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    records = []
    # 匹配 yaml 代码块
    pattern = re.compile(r"```yaml\s*\n(.*?)```", re.DOTALL)
    for match in pattern.finditer(content):
        block = match.group(1)
        try:
            parsed = yaml.safe_load(block)
            if isinstance(parsed, list):
                for rec in parsed:
                    if isinstance(rec, dict) and not _is_template_record(rec):
                        records.append(rec)
            elif isinstance(parsed, dict):
                # 单条记录的情况
                if not _is_template_record(parsed):
                    records.append(parsed)
        except yaml.YAMLError as e:
            print(f"警告：解析 {filepath} 中的 YAML 块失败: {e}")
    return records


def deduplicate_records(records: list[dict]) -> list[dict]:
    """按 id / reference_id 去重，保留第一次出现的记录。"""
    seen = set()
    result = []
    for r in records:
        key = r.get("id") or r.get("reference_id")
        if not key:
            continue
        if key in seen:
            continue
        seen.add(key)
        result.append(r)
    return result


def categorize_record(record: dict) -> str:
    """根据记录内容返回分类标签。"""
    key = (record.get("id") or record.get("reference_id", "")).lower()
    topics = record.get("topics", []) or []
    tags = record.get("tags", []) or []
    if isinstance(topics, str):
        topics = [topics]
    if isinstance(tags, str):
        tags = [tags]
    title = extract_title(record).lower()
    combined = " ".join(str(t).lower() for t in topics + tags) + " " + title + " " + key

    if any(x in combined for x in ["algorithm", "clrs", "knuth", "cormen", "ahuja", "motwani", "数据结构"]):
        return "算法基础"
    if any(x in combined for x in ["turing", "church", "computable", " Sipser ", "computation", "automata", "计算模型", "computability", "recursion"]):
        return "计算理论"
    if any(x in combined for x in ["complexity", "np", "p-np", "arora", "barak", "复杂度"]):
        return "复杂度理论"
    if any(x in combined for x in ["type theory", "lambda", "pierce", "barendregt", "martin-löf", "类型", "hott", "homotopy"]):
        return "类型理论与形式化方法"
    if any(x in combined for x in ["logic", "smt", "sat", "decision", "gentzen", "kripke", "gödel", "逻辑"]):
        return "逻辑系统"
    if any(x in combined for x in ["quantum", "nielsen", "preskill", "量子"]):
        return "量子计算"
    if any(x in combined for x in ["formal verification", "coq", "lean", "proof", "software foundations", "形式化", "验证"]):
        return "形式化验证"
    if any(x in combined for x in ["machine learning", "neural", "transformer", "federated", "graph neural", "强化学习", "gnn"]):
        return "机器学习"
    if any(x in combined for x in ["dynamic graph", "matching", "clustering", "steiner", "streaming", "sublinear", "图算法", "流算法"]):
        return "图算法与优化"
    return "综合引用"


def main():
    print("=" * 60)
    print("YAML 引用数据库 → BibTeX 转换工具")
    print("=" * 60)

    all_records = []

    # 1. 解析 references_database_2024_2025.yaml
    yaml_file = DOCS_DIR / "references_database_2024_2025.yaml"
    if yaml_file.exists():
        print(f"\n[1/3] 正在解析: {yaml_file.name}")
        recs = parse_yaml_file(yaml_file)
        print(f"       找到 {len(recs)} 条记录")
        all_records.extend(recs)
    else:
        print(f"\n[1/3] 跳过（文件不存在）: {yaml_file.name}")

    # 2. 解析引用规范与数据库.md 中的内嵌 YAML
    md_file = DOCS_DIR / "引用规范与数据库.md"
    if md_file.exists():
        print(f"\n[2/3] 正在解析: {md_file.name}")
        recs = parse_embedded_yaml_in_markdown(md_file)
        print(f"       找到 {len(recs)} 条记录")
        all_records.extend(recs)
    else:
        print(f"\n[2/3] 跳过（文件不存在）: {md_file.name}")

    # 去重
    all_records = deduplicate_records(all_records)
    print(f"\n[3/3] 去重后总计: {len(all_records)} 条唯一记录")

    if not all_records:
        print("\n错误：未找到任何可转换的记录。")
        sys.exit(1)

    # 按分类排序
    categorized = {}
    for rec in all_records:
        cat = categorize_record(rec)
        categorized.setdefault(cat, []).append(rec)

    # 生成 BibTeX 内容
    header_lines = [
        "% BibTeX Reference Database for FormalAlgorithm Project",
        "% Generated automatically from YAML databases",
        "% Migrated from YAML on 2026-04-29",
        "%",
        "% WARNING: Do not edit this file directly.",
        "%   To add or modify references, edit the source YAML files:",
        "%   - docs/references_database_2024_2025.yaml",
        "%   - docs/引用规范与数据库.md",
        "%   Then re-run: python scripts/convert_refs_to_bibtex.py",
        "%",
        "",
    ]

    body_lines = []
    # 按固定顺序输出分类
    category_order = [
        "算法基础",
        "计算理论",
        "复杂度理论",
        "类型理论与形式化方法",
        "逻辑系统",
        "形式化验证",
        "量子计算",
        "机器学习",
        "图算法与优化",
        "综合引用",
    ]

    for cat in category_order:
        if cat not in categorized:
            continue
        body_lines.append(f"% === {cat} ===")
        body_lines.append("")
        for rec in categorized[cat]:
            entry = build_bibtex_entry(rec)
            if entry:
                body_lines.append(entry)
                body_lines.append("")

    # 写入文件
    OUTPUT_BIB.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_BIB, "w", encoding="utf-8") as f:
        f.write("\n".join(header_lines + body_lines))

    print(f"\n✅ 成功生成: {OUTPUT_BIB}")
    print(f"   总计条目: {len(all_records)}")
    for cat in category_order:
        if cat in categorized:
            print(f"   - {cat}: {len(categorized[cat])} 条")


if __name__ == "__main__":
    main()
