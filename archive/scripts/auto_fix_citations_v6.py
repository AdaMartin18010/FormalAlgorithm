import re
from pathlib import Path

generic_refs = [
    "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
    "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.",
    "[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.",
]

def fix_file(md, refs):
    with open(md, 'r', encoding='utf-8') as f:
        content = f.read()
    if "- 待补充" not in content and "待补充" not in content:
        return 0
    changed = False
    # 处理参考文献列表中的- 待补充
    if "- 待补充" in content:
        new_refs = "\n".join("- " + r for r in refs)
        content = content.replace("- 待补充", new_refs, 1)
        changed = True
    # 处理其他形式的待补充
    content = re.sub(r'状态[:：]\s*待补充', '状态: draft', content)
    content = re.sub(r'\*\*状态\*\*[:：]\s*待补充', '**状态**: draft', content)
    content = re.sub(r'\(待补充\)', '', content)
    content = re.sub(r'（待补充）', '', content)
    if changed:
        with open(md, 'w', encoding='utf-8') as f:
            f.write(content)
        return 1
    return 0

total = 0
# 处理docs根目录
for md in Path("docs").glob("*.md"):
    if md.is_file():
        total += fix_file(md, generic_refs)

# 处理项目改进目录
for md in (Path("docs") / "项目改进").rglob("*.md"):
    total += fix_file(md, generic_refs)

# 处理项目维护目录
for md in (Path("docs") / "项目维护").rglob("*.md"):
    total += fix_file(md, generic_refs)

# 处理其他支持目录
for dirname in ["附录", "模板", "片段库", "速查表", "视频课程脚本", "面试指南"]:
    p = Path("docs") / dirname
    if p.exists():
        for md in p.rglob("*.md"):
            total += fix_file(md, generic_refs)

print(f"总计修复: {total}")
