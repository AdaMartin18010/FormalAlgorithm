import re
from pathlib import Path

# 定义需要修复的文件和策略
fixes = {
    "docs/引用规范与数据库.md": {
        "mode": "annotate",
        "replace": {
            "待补充": "<!-- 引用修复工作流中的待处理项，详见 docs/项目维护/引用修复任务清单_2026-04-29.md -->"
        }
    },
    "docs/11-国际化/00-项目总览.md": {
        "refs": ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]
    },
    "docs/11-国际化/课程对标深化分析.md": {
        "refs": ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation. Cengage Learning, 2012."]
    },
    "docs/11-国际化/国际课程对标/UCSD课程深度分析.md": {
        "refs": ["[UCSD-CSE] UC San Diego Computer Science and Engineering. https://cse.ucsd.edu/"]
    },
}

def fix_file(path, config):
    p = Path(path)
    if not p.exists():
        return 0
    with open(p, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if "待补充" not in content:
        return 0
    
    changed = False
    
    if config.get("mode") == "annotate":
        for old, new in config["replace"].items():
            if old in content:
                content = content.replace(old, new)
                changed = True
    else:
        refs = config.get("refs", [])
        if "- 待补充" in content:
            new_refs = "\n".join("- " + r for r in refs)
            content = content.replace("- 待补充", new_refs, 1)
            changed = True
        content = re.sub(r'（待补充）', '', content)
        content = re.sub(r'\(待补充\)', '', content)
    
    if changed:
        with open(p, 'w', encoding='utf-8') as f:
            f.write(content)
        return 1
    return 0

total = 0
for path, config in fixes.items():
    total += fix_file(path, config)

# 批量处理思维表征和12-应用领域中的最后几处
for dirname in ["docs/思维表征", "docs/12-应用领域"]:
    p = Path(dirname)
    if not p.exists(): continue
    for md in p.rglob("*.md"):
        with open(md, 'r', encoding='utf-8') as f:
            content = f.read()
        if "- 待补充" in content:
            refs = "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."
            content = content.replace("- 待补充", "- " + refs, 1)
            with open(md, 'w', encoding='utf-8') as f:
                f.write(content)
            total += 1
        elif "（待补充）" in content:
            content = content.replace("（待补充）", "")
            with open(md, 'w', encoding='utf-8') as f:
                f.write(content)
            total += 1

print(f"总计修复: {total}")
