import os, re

files = [
    ("01-命题逻辑.md", 646),
    ("02-一阶逻辑.md", 1147),
    ("03-直觉逻辑.md", 999),
    ("04-模态逻辑.md", 1089),
    ("06-线性逻辑.md", 1288),
    ("07-时序逻辑.md", 418),
]

entry_pattern = re.compile(r"^(?:\s*\d+\.\s+)(?:\[([^\]]+)\]\s+)?(.+?)\s*\((\d{4})(?:[-–—]\d{2,4})?\)\.(?:\"([^\"]+)\"|\*([^*]+)\*|(.+?))\.\s*(.+?)\.?\s*$")

def format_entry(num, author, year, title, venue):
    title = title.strip()
    venue = venue.strip()
    author = author.strip()
    return f"[{num}] {author}. {title}. {venue}, {year}."

for filename, refs_line in files:
    path = os.path.join("docs/06-逻辑系统", filename)
    with open(path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    body = "".join(lines[:refs_line-1])
    refs_text = "".join(lines[refs_line-1:])
    entries = []
    for line in refs_text.splitlines():
        m = entry_pattern.match(line)
        if m:
            key, author, year, t1, t2, t3, venue = m.groups()
            title = t1 or t2 or t3
            entries.append((key, author, year, title, venue))
    cited = []
    uncited = []
    for key, author, year, title, venue in entries:
        if key and f"[{key}]" in body:
            cited.append((key, author, year, title, venue))
        else:
            uncited.append((key, author, year, title, venue))
    ordered = cited + uncited
    num_map = {}
    for i, (key, _, _, _, _) in enumerate(ordered, 1):
        if key:
            num_map[key] = i
    for key, num in num_map.items():
        body = body.replace(f"[{key}]", f"[{num}]")
    refs_out = ["\n## 参考文献 / References\n\n"]
    for i, (key, author, year, title, venue) in enumerate(ordered, 1):
        refs_out.append(format_entry(i, author, year, title, venue) + "\n")
    refs_out.append("\n")
    new_text = body + "".join(refs_out)
    with open(path, "w", encoding="utf-8") as f:
        f.write(new_text)
    print(f"Done {filename}: {len(cited)} cited, {len(uncited)} uncited, total lines {len(new_text.splitlines())}")
