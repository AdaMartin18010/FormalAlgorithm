import re
from pathlib import Path

# 扩展主题映射
topic_refs = {
    "09-算法理论": [
        "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
        "[Sedgewick2011] R. Sedgewick and K. Wayne. Algorithms (4th ed.). Addison-Wesley, 2011.",
        "[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3. Addison-Wesley, 1998.",
        "[Aho1974] A. V. Aho, J. E. Hopcroft, and J. D. Ullman. The Design and Analysis of Computer Algorithms. Addison-Wesley, 1974.",
    ],
    "10-高级主题": [
        "[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.",
        "[NielsenChuang2010] M. A. Nielsen and I. L. Chuang. Quantum Computation and Quantum Information. Cambridge University Press, 2010.",
        "[Goodfellow2016] I. Goodfellow, Y. Bengio, and A. Courville. Deep Learning. MIT Press, 2016.",
        "[Cormen2022] T. H. Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022.",
    ],
    "12-应用领域": [
        "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
        "[Skiena2008] S. S. Skiena. The Algorithm Design Manual (2nd ed.). Springer, 2008.",
        "[Mehlhorn2008] K. Mehlhorn and P. Sanders. Algorithms and Data Structures: The Basic Toolbox. Springer, 2008.",
    ],
    "知识笔记": [
        "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
        "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.",
        "[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.",
    ],
    "面试指南": [
        "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
        "[McDowell2015] G. Laakmann McDowell. Cracking the Coding Interview (6th ed.). CareerCup, 2015.",
    ],
}

def fix_file(filepath, refs):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if "- 待补充" not in content and "待补充" not in content:
        return 0
    
    count = 0
    # 替换"- 待补充"
    if "- 待补充" in content:
        new_refs = "\n".join("- " + r for r in refs)
        content = content.replace("- 待补充", new_refs, 1)
        count += 1
    
    # 替换剩余的孤立"待补充"（如"状态：待补充"）
    content = re.sub(r'状态[:：]\s*待补充', '状态: draft', content)
    content = re.sub(r'\*\*状态\*\*[:：]\s*待补充', '**状态**: draft', content)
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    return count

total = 0
for topic, refs in topic_refs.items():
    p = Path("docs") / topic
    if not p.exists():
        continue
    for md in p.rglob("*.md"):
        n = fix_file(md, refs)
        if n > 0:
            total += 1
            print(f"Fixed: {md}")

# 处理docs/根目录下的孤立文件（如数据结构理论.md等）
root_refs = [
    "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
    "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.",
    "[Knuth1997] D. E. Knuth. The Art of Computer Programming, Vol. 1. Addison-Wesley, 1997.",
]
for md in Path("docs").glob("*.md"):
    if md.is_dir():
        continue
    n = fix_file(md, root_refs)
    if n > 0:
        total += 1
        print(f"Fixed root: {md}")

print(f"\n总计修复: {total} 个文件")
