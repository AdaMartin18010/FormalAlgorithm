import re
path = "docs/06-逻辑系统/04-模态逻辑.md"
with open(path,"r",encoding="utf-8") as f:
    lines = f.readlines()
body = "".join(lines[:1088])
refs_text = "".join(lines[1088:])
entry_pattern = re.compile(r"^(?:\s*\d+\.\s+)(?:\[([^\]]+)\]\s+)?(.+?)\s*\((\d{4})(?:[-–—]\d{2,4})?\)\.(?:\"([^\"]+)\"|\*([^*]+)\*|(.+?))\.\s*(.+?)\.?\s*$")
for line in refs_text.splitlines():
    m = entry_pattern.match(line)
    if m:
        key = m.group(1)
        print(repr(key), key in body if key else "no key")
