import re

for fname in ["05-多值逻辑理论.md", "08-高阶逻辑理论.md", "09-时序逻辑理论.md"]:
    with open(f"docs/06-逻辑系统/{fname}", "r", encoding="utf-8") as f:
        content = f.read()
    
    idx = content.rfind("## 参考文献")
    if idx < 0:
        idx = content.rfind("## 7. 参考文献")
    if idx < 0:
        idx = content.rfind("参考文献 / References")
    if idx < 0:
        idx = len(content)
    
    text_part = content[:idx]
    refs_part = content[idx:]
    
    # Find all author-year keys in the entire content to build mapping
    all_brackets = re.findall(r'\[([^\]]+)\]', content)
    author_year_pattern = re.compile(r'^[A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*$')
    
    all_keys = []
    for bracket_content in all_brackets:
        parts = [p.strip() for p in bracket_content.split(',')]
        for part in parts:
            if author_year_pattern.match(part) and part not in all_keys:
                all_keys.append(part)
    
    print(f"{fname}: keys={all_keys}")
    if not all_keys:
        continue
    
    mapping = {k: f"[{i+1}]" for i, k in enumerate(all_keys)}
    
    # Replace in text_part: handle both single keys and comma-separated lists
    for bracket_content in set(all_brackets):
        parts = [p.strip() for p in bracket_content.split(',')]
        if all(author_year_pattern.match(p) for p in parts):
            old = f"[{bracket_content}]"
            new = ", ".join(mapping[p] for p in parts)
            text_part = text_part.replace(old, new)
    
    # Replace in refs_part
    for k, num in mapping.items():
        for i in range(1, 20):
            refs_part = refs_part.replace(f"{i}. [{k}]", f"{i}. {num}")
    
    content = text_part + refs_part
    
    with open(f"docs/06-逻辑系统/{fname}", "w", encoding="utf-8") as f:
        f.write(content)
    
    # Verify
    with open(f"docs/06-逻辑系统/{fname}", "r", encoding="utf-8") as f:
        verify = f.read()
    vidx = verify.rfind("## 参考文献")
    vtext = verify[:vidx]
    remaining = re.findall(r'\[([A-Za-z\u00C0-\u017F\u0180-\u024F]+\d{4}[a-zA-Z0-9]*)\]', vtext)
    nums = re.findall(r'\[(\d+)\]', vtext)
    print(f"  -> remaining AY={sorted(set(remaining))}, nums={sorted(set(nums), key=int)}")
