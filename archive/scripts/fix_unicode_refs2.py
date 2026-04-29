import re

for fname in ["05-多值逻辑理论.md", "08-高阶逻辑理论.md", "09-时序逻辑理论.md"]:
    with open(f"docs/06-逻辑系统/{fname}", "r", encoding="utf-8") as f:
        content = f.read()
    
    author_year_pattern = re.compile(r'^[A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*$')
    
    # Find all bracketed contents
    all_brackets = re.findall(r'\[([^\]]+)\]', content)
    
    # Identify which bracket contents are purely citation lists
    citation_brackets = []
    for bracket_content in all_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        if all(author_year_pattern.match(p) for p in parts) and len(parts) >= 1:
            citation_brackets.append(bracket_content)
    
    # Extract unique keys
    author_keys = []
    for bracket_content in citation_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        for part in parts:
            if part not in author_keys:
                author_keys.append(part)
    
    print(f"{fname}: found {len(author_keys)} keys: {author_keys}")
    
    if not author_keys:
        print("  -> no conversion needed")
        continue
    
    mapping = {k: f"[{i+1}]" for i, k in enumerate(author_keys)}
    
    # Split content
    idx = content.find("参考文献")
    if idx < 0:
        idx = len(content)
    text_part = content[:idx]
    refs_part = content[idx:]
    
    # Replace only pure citation brackets in text
    for bracket_content in citation_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        old = f"[{bracket_content}]"
        new = ", ".join(mapping[p] for p in parts)
        text_part = text_part.replace(old, new)
    
    # Replace in references section
    for k, num in mapping.items():
        for i in range(1, 20):
            refs_part = refs_part.replace(f"{i}. [{k}]", f"{i}. {num}")
    
    content = text_part + refs_part
    
    with open(f"docs/06-逻辑系统/{fname}", "w", encoding="utf-8") as f:
        f.write(content)
    
    print(f"  -> converted")
