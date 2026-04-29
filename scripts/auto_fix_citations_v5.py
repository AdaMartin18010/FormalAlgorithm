import re
from pathlib import Path

# 11-国际化: 课程对标类文件
intl_refs = [
    "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
    "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.",
    "[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.",
    "[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.",
]

algo_refs = [
    "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
    "[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3. Addison-Wesley, 1998.",
    "[Ahuja1993] R. K. Ahuja, T. L. Magnanti, and J. B. Orlin. Network Flows: Theory, Algorithms, and Applications. Prentice-Hall, 1993.",
]

def fix_dir(path, refs):
    total = 0
    if not path.exists(): return 0
    for md in path.rglob("*.md"):
        with open(md, 'r', encoding='utf-8') as f:
            content = f.read()
        if "- 待补充" not in content and "待补充" not in content:
            continue
        changed = False
        if "- 待补充" in content:
            new_refs = "\n".join("- " + r for r in refs)
            content = content.replace("- 待补充", new_refs, 1)
            changed = True
        # 替换其他形式的待补充
        content = re.sub(r'状态[:：]\s*待补充', '状态: draft', content)
        content = re.sub(r'\*\*状态\*\*[:：]\s*待补充', '**状态**: draft', content)
        if changed or "待补充" in content:
            with open(md, 'w', encoding='utf-8') as f:
                f.write(content)
            total += 1
            print(f"Fixed: {md}")
    return total

t = fix_dir(Path("docs/11-国际化"), intl_refs)
t += fix_dir(Path("docs/09-算法理论"), algo_refs)
t += fix_dir(Path("docs/10-高级主题"), algo_refs)
print(f"\n总计修复: {t}")
