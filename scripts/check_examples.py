import re

path = 'docs/08-实现示例/01-Rust实现.md'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

blocks = re.findall(r'```rust\n(.*?)```', content, re.DOTALL)
for i, block in enumerate(blocks):
    if 'merge' in block.lower() or '归并' in block:
        print(f'=== Block {i} ===')
        print(block[:500])
        print('...')
        print()
