import re

with open("docs/06-逻辑系统/09-时序逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

keys = re.findall(r'\[([A-Z][a-zA-Z0-9]+\d{4}[a-zA-Z0-9]*)\]', content)
unique_keys = []
for k in keys:
    if k not in unique_keys:
        unique_keys.append(k)

print("Found keys:", unique_keys)

mapping = {k: f"[{i+1}]" for i, k in enumerate(unique_keys)}

for k, num in mapping.items():
    content = content.replace(f"[{k}]", num)

for k, num in mapping.items():
    for i in range(1, 15):
        content = content.replace(f"{i}. [{k}]", f"{i}. {num}")

with open("docs/06-逻辑系统/09-时序逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("09 reference conversion done, total refs:", len(unique_keys))
