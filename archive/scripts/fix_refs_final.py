import re

for fname in ["05-多值逻辑理论.md", "08-高阶逻辑理论.md", "09-时序逻辑理论.md"]:
    with open(f"docs/06-逻辑系统/{fname}", "r", encoding="utf-8") as f:
        content = f.read()
    
    author_year_pattern = re.compile(r'^[A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*$')
    all_brackets = re.findall(r'\[([^\]]+)\]', content)
    
    citation_brackets = []
    for bracket_content in all_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        if all(author_year_pattern.match(p) for p in parts) and len(parts) >= 1:
            citation_brackets.append(bracket_content)
    
    # Deduplicate
    seen = set()
    unique_citation_brackets = []
    for cb in citation_brackets:
        if cb not in seen:
            seen.add(cb)
            unique_citation_brackets.append(cb)
    
    print(f"{fname}: {len(unique_citation_brackets)} unique citation brackets")
    
    if not unique_citation_brackets:
        continue
    
    # Find last occurrence of 参考文献 or References header
    idx = content.rfind("## 参考文献")
    if idx < 0:
        idx = content.rfind("## 7. 参考文献")
    if idx < 0:
        idx = content.rfind("参考文献 / References")
    if idx < 0:
        idx = len(content)
    
    text_part = content[:idx]
    refs_part = content[idx:]
    
    for bracket_content in unique_citation_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        old = f"[{bracket_content}]"
        new = ", ".join(f"[{p}]" for p in parts)  # keep brackets around each number
        text_part = text_part.replace(old, new)
    
    # Now extract keys and build mapping for references section
    author_keys = []
    for bracket_content in unique_citation_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        for part in parts:
            if part not in author_keys:
                author_keys.append(part)
    
    mapping = {k: f"[{i+1}]" for i, k in enumerate(author_keys)}
    
    for k, num in mapping.items():
        for i in range(1, 20):
            refs_part = refs_part.replace(f"{i}. [{k}]", f"{i}. {num}")
    
    content = text_part + refs_part
    
    with open(f"docs/06-逻辑系统/{fname}", "w", encoding="utf-8") as f:
        f.write(content)
    
    print(f"  -> converted {len(mapping)} keys")
