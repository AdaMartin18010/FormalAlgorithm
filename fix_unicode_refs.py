import re

for fname in ["05-多值逻辑理论.md", "08-高阶逻辑理论.md", "09-时序逻辑理论.md"]:
    with open(f"docs/06-逻辑系统/{fname}", "r", encoding="utf-8") as f:
        content = f.read()
    
    # Find all citation keys including accented ones and comma-separated
    pattern = r'\[([^\]]+)\]'
    all_brackets = re.findall(pattern, content)
    
    # Extract individual author-year keys
    author_keys = []
    for bracket_content in all_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        for part in parts:
            # Check if it looks like AuthorYear
            if re.match(r'^[A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*$', part):
                if part not in author_keys:
                    author_keys.append(part)
    
    print(f"{fname}: found {len(author_keys)} keys: {author_keys}")
    
    if not author_keys:
        continue
    
    mapping = {k: f"[{i+1}]" for i, k in enumerate(author_keys)}
    
    # Replace citations in text (before 参考文献)
    idx = content.find("参考文献")
    if idx < 0:
        idx = len(content)
    text_part = content[:idx]
    refs_part = content[idx:]
    
    for bracket_content in all_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        if all(p in mapping for p in parts if re.match(r'^[A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*$', p)):
            # All parts are author-year keys
            new_parts = [mapping[p] for p in parts]
            old = f"[{bracket_content}]"
            new = ", ".join(new_parts)
            text_part = text_part.replace(old, new)
    
    # Also replace in references section
    for k, num in mapping.items():
        for i in range(1, 20):
            refs_part = refs_part.replace(f"{i}. [{k}]", f"{i}. {num}")
    
    content = text_part + refs_part
    
    with open(f"docs/06-逻辑系统/{fname}", "w", encoding="utf-8") as f:
        f.write(content)
    
    print(f"  -> converted to {len(mapping)} numbered refs")
