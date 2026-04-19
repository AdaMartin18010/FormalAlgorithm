import re

with open("docs/06-逻辑系统/05-多值逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

# Find all citation keys in order of appearance
keys = re.findall(r'\[([A-Z][a-zA-Z0-9]+\d{4}[a-zA-Z0-9]*)\]', content)
unique_keys = []
for k in keys:
    if k not in unique_keys:
        unique_keys.append(k)

print("Found keys:", unique_keys)

# Build replacement mapping
mapping = {k: f"[{i+1}]" for i, k in enumerate(unique_keys)}

# Replace all citations in text
for k, num in mapping.items():
    content = content.replace(f"[{k}]", num)

# Also replace in references section
for k, num in mapping.items():
    content = content.replace(f"1. [{k}]", f"1. {num}")
    content = content.replace(f"2. [{k}]", f"2. {num}")
    content = content.replace(f"3. [{k}]", f"3. {num}")
    content = content.replace(f"4. [{k}]", f"4. {num}")
    content = content.replace(f"5. [{k}]", f"5. {num}")
    content = content.replace(f"6. [{k}]", f"6. {num}")
    content = content.replace(f"7. [{k}]", f"7. {num}")
    content = content.replace(f"8. [{k}]", f"8. {num}")
    content = content.replace(f"9. [{k}]", f"9. {num}")
    content = content.replace(f"10. [{k}]", f"10. {num}")

with open("docs/06-逻辑系统/05-多值逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("05 reference conversion done, total refs:", len(unique_keys))
