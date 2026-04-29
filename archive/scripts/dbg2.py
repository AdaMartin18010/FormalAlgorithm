path = "docs/06-逻辑系统/04-模态逻辑.md"
with open(path,"r",encoding="utf-8") as f:
    lines = f.readlines()
refs_text = "".join(lines[1088:])
for line in refs_text.splitlines()[:20]:
    print(repr(line))
